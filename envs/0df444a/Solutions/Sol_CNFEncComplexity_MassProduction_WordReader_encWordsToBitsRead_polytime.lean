-- Prove2me | solution 1 for CNFEncComplexity.MassProduction.WordReader.encWordsToBitsRead_polytime
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T06:44:02.873386+00:00
-- url     : https://prove2.me/submissions/563d8d65-05da-4f8a-aabd-8aa4bfeb1031

import Definitions.Def_CNFEncComplexity_encWords
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

set_option linter.all false
set_option maxHeartbeats 4000000

namespace CNFEncComplexity.MassProduction.StreamMachine

open Turing StateTransition

/-- Two external tapes and a configurable finite collection of work tapes. -/
inductive Tape (K : Type)
  | input
  | output
  | work (k : K)
  deriving DecidableEq, Fintype

/-- The input and work tapes carry the three symbols of the sparse input encoding. -/
abbrev Gamma {K : Type} : Tape K → Type
  | .input => Fin 3
  | .output => Bool
  | .work _ => Fin 3

/-- A finite-control instruction that performs at most one stack operation. -/
inductive Cmd (K PC σ : Type)
  | push (k : Tape K) (symbol : σ → Gamma k) (next : σ → PC)
  | pop (k : Tape K) (update : σ → Option (Gamma k) → σ) (next : σ → PC)
  | peek (k : Tape K) (update : σ → Option (Gamma k) → σ) (next : σ → PC)
  | load (update : σ → σ) (next : σ → PC)
  | jump (next : σ → PC)
  | halt

/-- In an abstract configuration, a missing program counter means the machine has halted. -/
structure Cfg (K PC σ : Type) where
  l : Option PC
  var : σ
  input : List (Fin 3)
  output : List Bool
  work : K → List (Fin 3)

namespace Cfg

def get {K PC σ : Type} (c : Cfg K PC σ) (k : Tape K) : List (Gamma k) :=
  match k with
  | .input => c.input
  | .output => c.output
  | .work k => c.work k

def set {K PC σ : Type} [DecidableEq K] (c : Cfg K PC σ) (k : Tape K)
    (v : List (Gamma k)) : Cfg K PC σ :=
  match k with
  | .input => { c with input := v }
  | .output => { c with output := v }
  | .work k => { c with work := Function.update c.work k v }

end Cfg

def runCmd {K PC σ : Type} [DecidableEq K] (c : Cfg K PC σ) (cmd : Cmd K PC σ) :
    Cfg K PC σ :=
  match cmd with
  | .push k symbol next =>
      { c.set k (symbol c.var :: c.get k) with l := some (next c.var) }
  | .pop k update next =>
      let var := update c.var (c.get k).head?
      { c.set k (c.get k).tail with l := some (next var), var := var }
  | .peek k update next =>
      let var := update c.var (c.get k).head?
      { c with l := some (next var), var := var }
  | .load update next =>
      let var := update c.var
      { c with l := some (next var), var := var }
  | .jump next => { c with l := some (next c.var) }
  | .halt => { c with l := none }

/-- The one-step semantics used to verify programs, including the program counter. -/
def step {K PC σ : Type} [DecidableEq K] (prog : PC → Cmd K PC σ)
    (c : Cfg K PC σ) : Option (Cfg K PC σ) :=
  c.l.map (fun l => runCmd c (prog l))

/-- Emit one block of native TM2 instructions, ending at the next program counter. -/
def compileCmd {K PC σ : Type} (cmd : Cmd K PC σ) : TM2.Stmt (@Gamma K) PC σ :=
  match cmd with
  | .push k symbol next => .push k symbol (.goto next)
  | .pop k update next => .pop k update (.goto next)
  | .peek k update next => .peek k update (.goto next)
  | .load update next => .load update (.goto next)
  | .jump next => .goto next
  | .halt => .halt

def toNative {K PC σ : Type} (c : Cfg K PC σ) : TM2.Cfg (@Gamma K) PC σ :=
  ⟨c.l, c.var, c.get⟩

private theorem get_set {K PC σ : Type} [DecidableEq K] (c : Cfg K PC σ)
    (k : Tape K) (v : List (Gamma k)) :
    (c.set k v).get = Function.update c.get k v := by
  funext j
  cases k <;> cases j <;>
    simp [Cfg.set, Cfg.get, Function.update]
  rename_i k j
  by_cases h : j = k
  · subst j
    simp
  · rw [if_neg h, dif_neg h]

theorem compileCmd_exact {K PC σ : Type} [DecidableEq K] (c : Cfg K PC σ)
    (cmd : Cmd K PC σ) :
    toNative (runCmd c cmd) = TM2.stepAux (compileCmd cmd) c.var c.get := by
  cases cmd with
  | push k f next =>
      simp only [runCmd, compileCmd, TM2.stepAux]
      have hvar : (c.set k (f c.var :: c.get k)).var = c.var := by cases k <;> rfl
      unfold toNative
      rw [hvar]
      exact congrArg (TM2.Cfg.mk _ _) (get_set c k (f c.var :: c.get k))
  | pop k update next =>
      simp only [runCmd, compileCmd, TM2.stepAux]
      exact congrArg (TM2.Cfg.mk _ _) (get_set c k (c.get k).tail)
  | peek => rfl
  | load => rfl
  | jump => rfl
  | halt => rfl

theorem step_exact {K PC σ : Type} [DecidableEq K] (prog : PC → Cmd K PC σ)
    (c : Cfg K PC σ) :
    TM2.step (compileCmd ∘ prog) (toNative c) = (step prog c).map toNative := by
  cases c with
  | mk pc var input output work =>
    cases pc with
    | none => rfl
    | some pc =>
      exact congrArg some (compileCmd_exact ⟨some pc, var, input, output, work⟩ (prog pc)).symm

/-- Starting configuration for a word, with all work tapes empty. -/
def start {K PC σ : Type} (main : PC) (initial : σ) (input : List (Fin 3)) : Cfg K PC σ :=
  ⟨some main, initial, input, [], fun _ => []⟩

/-- Halting configuration, with only the output tape nonempty. -/
def finish {K PC σ : Type} (initial : σ) (output : List Bool) : Cfg K PC σ :=
  ⟨none, initial, [], output, fun _ => []⟩

/-- The native TM2 has the same control labels and internal state as the program. -/
abbrev compile {K PC σ : Type} [DecidableEq K] [Fintype K] [Fintype PC] [Fintype σ]
    (main : PC) (initial : σ) (prog : PC → Cmd K PC σ) : FinTM2 where
  K := Tape K
  k₀ := .input
  k₁ := .output
  Γ := Gamma
  Λ := PC
  main := main
  σ := σ
  initialState := initial
  Γk₀Fin := inferInstanceAs (Fintype (Fin 3))
  m := compileCmd ∘ prog

@[simp] theorem start_exact {K PC σ : Type} [DecidableEq K] [Fintype K] [Fintype PC] [Fintype σ]
    (main : PC) (initial : σ) (prog : PC → Cmd K PC σ) (input : List (Fin 3)) :
    initList (compile main initial prog) input = toNative (start (K := K) main initial input) := by
  change (⟨some main, initial, _⟩ : TM2.Cfg (@Gamma K) PC σ) = _
  congr 1
  funext k
  cases k <;> rfl

@[simp] theorem finish_exact {K PC σ : Type} [DecidableEq K] [Fintype K] [Fintype PC] [Fintype σ]
    (main : PC) (initial : σ) (prog : PC → Cmd K PC σ) (output : List Bool) :
    haltList (compile main initial prog) output = toNative (finish (K := K) (PC := PC) initial output) := by
  change (⟨none, initial, _⟩ : TM2.Cfg (@Gamma K) PC σ) = _
  congr 1
  funext k
  cases k <;> rfl

theorem iterate_exact {K PC σ : Type} [DecidableEq K] (prog : PC → Cmd K PC σ) (n : ℕ)
    (c : Option (Cfg K PC σ)) :
    (flip bind (TM2.step (compileCmd ∘ prog)))^[n] (c.map toNative) =
      ((flip bind (step prog))^[n] c).map toNative := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases c with
      | none => exact ih none
      | some c =>
        change (flip bind (TM2.step (compileCmd ∘ prog)))^[n]
          (TM2.step (compileCmd ∘ prog) (toNative c)) = _
        rw [step_exact]
        exact ih (step prog c)

/-- A time-bounded abstract evaluation certifies a real finite multi-tape Turing machine. -/
def certify {K PC σ α β : Type} [DecidableEq K] [Fintype K] [Fintype PC] [Fintype σ]
    (main : PC) (initial : σ) (prog : PC → Cmd K PC σ)
    (encodeInput : α → List (Fin 3)) (encodeOutput : β → List Bool) (f : α → β)
    (time : Polynomial ℕ)
    (proof : ∀ a, EvalsToInTime (step prog) (start main initial (encodeInput a))
      (some (finish initial (encodeOutput (f a)))) (time.eval (encodeInput a).length)) :
    TM2ComputableInPolyTime encodeInput encodeOutput f where
  tm := compile main initial prog
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time
  outputsFun a := by
    let p := proof a
    refine ⟨⟨p.steps, ?_⟩, p.steps_le_m⟩
    have hi : List.map (id : Fin 3 → Fin 3) (encodeInput a) = encodeInput a := List.map_id _
    have ho : List.map (id : Bool → Bool) (encodeOutput (f a)) = encodeOutput (f a) := List.map_id _
    change (flip bind (TM2.step (compileCmd ∘ prog)))^[p.steps]
      (some (initList (compile main initial prog) (List.map (id : Fin 3 → Fin 3) (encodeInput a)))) =
      some (haltList (compile main initial prog) (List.map (id : Bool → Bool) (encodeOutput (f a))))
    rw [hi, ho, start_exact, finish_exact]
    have h := iterate_exact prog p.steps (some (start main initial (encodeInput a)))
    rw [p.evals_in_steps] at h
    exact h

end CNFEncComplexity.MassProduction.StreamMachine
namespace CNFEncComplexity.MassProduction.WordReader

open CNFEncComplexity.MassProduction.StreamMachine StateTransition Turing.MultiTapeTM Polynomial

/-- The native list encoding doubles each input bit into a prefix and a bit,
and uses a single false marker for each ternary separator. -/
def emit (s : Fin 3) : List Bool := if s = 2 then [false] else [true,s = 1]

def toBits (input : List (Fin 3)) : List Bool := input.flatMap emit

theorem toBits_encWords (words : List (List Bool)) :
    toBits (encWords words) = encList encBits words := by
  have hbit (b : Bool) : emit (bitSym b) = [true,b] := by cases b <;> rfl
  have hsep : emit 2 = [false] := rfl
  induction words with
  | nil => rfl
  | cons w ws ih =>
    simp only [toBits,encWords,List.flatMap_cons,List.flatMap_append,List.flatMap_map,hbit,hsep,
      List.flatMap_nil,List.append_nil,encList_cons]
    change w.flatMap (fun b => [true,b]) ++ [false] ++ toBits (encWords ws) =
      frame w ++ encList encBits ws
    rw [ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
private inductive PC
  | read | prefix | digit | sep | take | put | reset | halt
  deriving DecidableEq, Fintype

private abbrev Var := Option (Fin 3)
private abbrev Config := Cfg Unit PC Var

private def code : PC → Cmd Unit PC Var
  | .read => .pop .input (fun _ v => v) (fun v =>
      if v = none then .take else if v = some 2 then .sep else .prefix)
  | .prefix => .push (.work ()) (fun _ => 1) (fun _ => .digit)
  | .digit => .push (.work ()) (fun v => v.getD 0) (fun _ => .read)
  | .sep => .push (.work ()) (fun _ => 0) (fun _ => .read)
  | .take => .pop (.work ()) (fun _ v => v) (fun v => if v.isSome then .put else .reset)
  | .put => .push .output (fun v => v = some 1) (fun _ => .take)
  | .reset => .load (fun _ => none) (fun _ => .halt)
  | .halt => .halt

private abbrev iter := flip bind (step code)

private def reading (v : Var) (inp : List (Fin 3)) (rev : List Bool) : Config :=
  ⟨some .read,v,inp,[],fun _ => rev.map bitSym⟩

private def turning (v : Var) (rev out : List Bool) : Config :=
  ⟨some .take,v,[],out,fun _ => rev.map bitSym⟩

private def scanStepCost (s : Fin 3) : ℕ := if s = 2 then 2 else 3

private theorem scanStep (s : Fin 3) (v : Var) (inp : List (Fin 3)) (rev : List Bool) :
    iter^[scanStepCost s] (some (reading v (s::inp) rev)) =
      some (reading (some s) inp ((emit s).reverse ++ rev)) := by
  fin_cases s <;> rfl

private def scanCost : List (Fin 3) → ℕ
  | [] => 0
  | s :: ss => scanCost ss + scanStepCost s

private def finalVar : List (Fin 3) → Var → Var
  | [],v => v
  | s::ss,_ => finalVar ss (some s)

private theorem scan (inp : List (Fin 3)) (v : Var) (rev : List Bool) :
    iter^[scanCost inp] (some (reading v inp rev)) =
      some (reading (finalVar inp v) [] ((toBits inp).reverse ++ rev)) := by
  induction inp generalizing v rev with
  | nil => rfl
  | cons s inp ih =>
    rw [scanCost,Function.iterate_add_apply,scanStep,ih]
    simp only [finalVar,toBits,List.flatMap_cons,List.reverse_append,List.append_assoc]

private theorem turn (rev out : List Bool) (v : Var) :
    iter^[2*rev.length+3] (some (turning v rev out)) =
      some (finish (PC := PC) none (rev.reverse ++ out)) := by
  induction rev generalizing out v with
  | nil => rfl
  | cons b rev ih =>
    simp only [List.length_cons]
    have ht : 2*(rev.length+1)+3 = (2*rev.length+3)+2 := by omega
    rw [ht,Function.iterate_add_apply]
    have hstep : iter^[2] (some (turning v (b::rev) out)) =
        some (turning (some (bitSym b)) rev (b::out)) := by cases b <;> rfl
    rw [hstep,ih]
    simp [List.reverse_cons,List.append_assoc]

private theorem scanCost_le (inp : List (Fin 3)) : scanCost inp ≤ 3*inp.length := by
  induction inp with
  | nil => rfl
  | cons s inp ih =>
    simp only [scanCost,List.length_cons]
    have ht : scanStepCost s ≤ 3 := by simp [scanStepCost]; split <;> decide
    omega

private theorem toBits_length (inp : List (Fin 3)) : (toBits inp).length ≤ 2*inp.length := by
  induction inp with
  | nil => rfl
  | cons s inp ih =>
    simp only [toBits,List.flatMap_cons,List.length_append,List.length_cons] at ih ⊢
    have ht : (emit s).length ≤ 2 := by unfold emit; split <;> simp
    omega

private def steps (inp : List (Fin 3)) :
    EvalsToInTime (step code) (start .read none inp) (some (finish (PC:=PC) none (toBits inp)))
      (7*inp.length+4) := by
  let middle := (toBits inp).reverse
  let q1 := reading (finalVar inp none) [] middle
  let q2 := turning none middle []
  have hScan : iter^[scanCost inp] (some (start .read none inp)) = some q1 := by
    simpa only [reading,List.map_nil,List.append_nil,start,q1,middle] using scan inp none []
  have hTransfer : iter^[1] (some q1) = some q2 := by
    rw [Function.iterate_one]
    rfl
  have hReverse : iter^[2*middle.length+3] (some q2) = some (finish (PC:=PC) none (toBits inp)) := by
    simpa only [middle,List.reverse_reverse,List.append_nil,q2] using turn middle [] none
  let n := ((2*middle.length+3)+1)+scanCost inp
  refine ⟨⟨n,?_⟩,?_⟩
  · change iter^[n] (some (start .read none inp)) = _
    dsimp only [n]
    simp only [iter] at hScan hTransfer hReverse ⊢
    rw [Function.iterate_add_apply,hScan,Function.iterate_add_apply,hTransfer,hReverse]
  · have hs := scanCost_le inp
    have hL := toBits_length inp
    dsimp only [n,middle]
    simp only [List.length_reverse]
    omega

/-- The same stream transducer regarded as a reader returning the word list. -/
theorem _root_.solution {α : Type} (words : α → List (List Bool)) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun a => encWords (words a)) (encList encBits) words) := by
  refine ⟨certify (K := Unit) .read none code
    (fun a => encWords (words a)) (encList encBits) words
    (C 7 * X + C 4) (fun a => ?_)⟩
  simpa only [eval_add,eval_mul,eval_C,eval_X,toBits_encWords] using steps (encWords (words a))

end CNFEncComplexity.MassProduction.WordReader
