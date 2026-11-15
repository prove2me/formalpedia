-- Prove2me | solution 1 for CNFEncComplexity.teutschNbr_polytime
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-14T18:37:51.359701+00:00
-- url     : https://prove2.me/submissions/381fab3e-1983-4b5b-aeb5-70c01c8dfd88

import Definitions.Def_CNFEncComplexity_encNbrIn
import Definitions.Def_CNFEncComplexity_teutschNbr
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Basic
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Option
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas
import Definitions.Def_TimeSpaceMA_RAM
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.DeriveFintype
import Theorems.Thm_Turing_TM2ComputableInPolyTime_comp_of_polytime

namespace CNFEncComplexity.SparseMachine

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

end CNFEncComplexity.SparseMachine

namespace CNFEncComplexity.SparseMachine

open StateTransition

/-- Lift a single abstract-machine transition into a time-bound certificate. -/
def take_step {K PC σ : Type} [DecidableEq K] (prog : PC → Cmd K PC σ)
    {a b : Cfg K PC σ} (h : step prog a = some b) :
    EvalsToInTime (step prog) a (some b) 1 :=
  ⟨⟨1, by rw [Function.iterate_one]; exact h⟩, le_rfl⟩

/-- Increase the time bound on a verified evaluation. -/
def weaken {K PC σ : Type} [DecidableEq K] {prog : PC → Cmd K PC σ}
    {a : Cfg K PC σ} {b : Option (Cfg K PC σ)} {m n : ℕ}
    (h : EvalsToInTime (step prog) a b m) (hmn : m ≤ n) :
    EvalsToInTime (step prog) a b n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hmn⟩

/-- A bounded prefix followed by a bounded suffix takes the sum of their budgets. -/
def then_run {K PC σ : Type} [DecidableEq K] {prog : PC → Cmd K PC σ}
    {a b : Cfg K PC σ} {c : Option (Cfg K PC σ)} {m n : ℕ}
    (ab : EvalsToInTime (step prog) a (some b) m)
    (bc : EvalsToInTime (step prog) b c n) :
    EvalsToInTime (step prog) a c (m + n) :=
  weaken (EvalsToInTime.trans (step prog) m n a b c ab bc) (by omega)

/-- The initial and final bounds for repeatedly executing a verified transition. -/
def loop_run {K PC σ : Type} [DecidableEq K] {prog : PC → Cmd K PC σ}
    (state : ℕ → Cfg K PC σ) (cost : ℕ)
    (each : ∀ i, EvalsToInTime (step prog) (state i) (some (state (i + 1))) cost)
    (n : ℕ) :
    EvalsToInTime (step prog) (state 0) (some (state n)) (n * cost) := by
  induction n with
  | zero => simpa only [Nat.zero_mul] using EvalsToInTime.refl (step prog) (state 0)
  | succ n ih => simpa only [Nat.succ_mul] using then_run ih (each n)

/-- The same loop rule for a family with a finite range of valid indices. -/
def bounded_loop_run {K PC σ : Type} [DecidableEq K] {prog : PC → Cmd K PC σ}
    (n : ℕ) (state : Fin (n + 1) → Cfg K PC σ) (cost : ℕ)
    (each : ∀ i : Fin n, EvalsToInTime (step prog) (state i.castSucc) (some (state i.succ)) cost) :
    EvalsToInTime (step prog) (state 0) (some (state (Fin.last n))) (n * cost) := by
  let extState (i : ℕ) : Cfg K PC σ := if hi : i ≤ n then state ⟨i, by omega⟩ else state (Fin.last n)
  have ext_step (i : ℕ) (hi : i < n) :
      EvalsToInTime (step prog) (extState i) (some (extState (i + 1))) cost := by
    have h₁ : i ≤ n := hi.le
    have h₂ : i + 1 ≤ n := hi
    have e₁ : extState i = state (Fin.castSucc ⟨i, hi⟩) := by simp [extState, h₁]
    have e₂ : extState (i + 1) = state (Fin.succ ⟨i, hi⟩) := by simp [extState, h₂]
    rw [e₁, e₂]
    exact each ⟨i, hi⟩
  have run (k : ℕ) (hk : k ≤ n) :
      EvalsToInTime (step prog) (extState 0) (some (extState k)) (k * cost) := by
    induction k with
    | zero => simpa only [Nat.zero_mul] using EvalsToInTime.refl (step prog) (extState 0)
    | succ k ih =>
        simpa only [Nat.succ_mul] using then_run (ih (by omega)) (ext_step k (by omega))
  have e₀ : extState 0 = state 0 := by
    simp [extState]
  have en : extState n = state (Fin.last n) := by
    simp [extState, Fin.last]
  rw [← e₀, ← en]
  exact run n le_rfl

end CNFEncComplexity.SparseMachine

namespace CNFEncComplexity.NeighborInput

open SparseMachine StateTransition

set_option backward.isDefEq.respectTransparency false in
inductive Field
  | first | second | third | last
  deriving DecidableEq, Fintype

def Field.next : Field → Field
  | .first => .second
  | .second => .third
  | .third => .last
  | .last => .last

set_option backward.isDefEq.respectTransparency false in
inductive PC
  | read (field : Field)
  | prefix (field : Field)
  | digit (field : Field)
  | sep (field : Field)
  | take | put | reset | halt
  deriving DecidableEq, Fintype

abbrev S := Option (Fin 3)
abbrev Config := Cfg Unit PC S

def code : PC → Cmd Unit PC S
  | .read f => .pop .input (fun _ v => v) (fun symbol =>
      if symbol.isNone then .take else
        if symbol = some 2 then (if f = .last then .take else .sep f)
        else (if f = .last then .digit f else .prefix f))
  | .prefix f => .push (.work ()) (fun _ => 1) (fun _ => .digit f)
  | .digit f => .push (.work ()) (fun s => s.getD 0) (fun _ => .read f)
  | .sep f => .push (.work ()) (fun _ => 0) (fun _ => .read f.next)
  | .take => .pop (.work ()) (fun _ v => v)
      (fun symbol => if symbol.isSome then .put else .reset)
  | .put => .push .output (fun s => s = some 1) (fun _ => .take)
  | .reset => .load (fun _ => none) (fun _ => .halt)
  | .halt => .halt

def packedBits (w : List Bool) : List Bool := w.flatMap (fun b => [true,b]) ++ [false]

def directEncoding (q : ℕ × ℕ × ℕ × ℕ) : List Bool :=
  packedBits (binWord q.1) ++ packedBits (binWord q.2.1) ++
  packedBits (binWord q.2.2.1) ++ binWord q.2.2.2

abbrev iter := flip bind (step code)

def reading (f : Field) (var : S) (input : List (Fin 3)) (acc : List (Fin 3)) : Config :=
  ⟨some (.read f), var, input, [], fun _ => acc⟩

def turning (next : PC) (var : S) (input acc : List (Fin 3)) (out : List Bool) : Config :=
  ⟨some next, var, input, out, fun _ => acc⟩

private theorem bitSym_zero_or_one (b : Bool) : bitSym b ≠ 2 := by cases b <;> decide

private theorem transition_read_early (f : Field) (hf : f ≠ .last)
    (b : Bool) (rest acc : List (Fin 3)) (s : S) :
    iter^[3] (some (reading f s (bitSym b :: rest) acc)) =
      some (reading f (some (bitSym b)) rest (bitSym b :: 1 :: acc)) := by
  cases f <;> cases b <;> first | contradiction | rfl

private theorem transition_read_last
    (b : Bool) (rest acc : List (Fin 3)) (s : S) :
    iter^[2] (some (reading .last s (bitSym b :: rest) acc)) =
      some (reading .last (some (bitSym b)) rest (bitSym b :: acc)) := by
  cases b <;> rfl

private theorem transition_separator (f : Field) (hf : f ≠ .last)
    (rest acc : List (Fin 3)) (s : S) :
    iter^[2] (some (reading f s (2 :: rest) acc)) =
      some (reading f.next (some 2) rest (0 :: acc)) := by
  cases f <;> first | contradiction | rfl

private theorem transition_last_separator (acc : List (Fin 3)) (s : S) :
    iter^[1] (some (reading .last s [2] acc)) = some (turning .take (some 2) [] acc []) :=
  rfl

private theorem scan_early (f : Field) (hf : f ≠ .last) (w : List Bool)
    (rest acc : List (Fin 3)) (s : S) :
    iter^[3 * w.length + 2] (some (reading f s (w.map bitSym ++ [2] ++ rest) acc)) =
      some (reading f.next (some 2) rest ((packedBits w).reverse.map bitSym ++ acc)) := by
  induction w generalizing s acc with
  | nil => simpa [packedBits, bitSym] using transition_separator f hf rest acc s
  | cons b w ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [show 3 * (w.length + 1) + 2 = (3 * w.length + 2) + 3 by omega,
      Function.iterate_add_apply, transition_read_early f hf, ih]
    simp [packedBits, List.reverse_append, List.append_assoc, bitSym]

private theorem scan_last (w : List Bool) (acc : List (Fin 3)) (s : S) :
    iter^[2 * w.length + 1] (some (reading .last s (w.map bitSym ++ [2]) acc)) =
      some (turning .take (some 2) [] (w.reverse.map bitSym ++ acc) []) := by
  induction w generalizing s acc with
  | nil => exact transition_last_separator acc s
  | cons b w ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [show 2 * (w.length + 1) + 1 = (2 * w.length + 1) + 2 by omega,
      Function.iterate_add_apply, transition_read_last, ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem turn (word : List Bool) (out : List Bool) (s : S) :
    iter^[2 * word.length + 3] (some (turning .take s [] (word.map bitSym) out)) =
      some (finish none (word.reverse ++ out)) := by
  induction word generalizing out s with
  | nil => rfl
  | cons b w ih =>
    simp only [List.map_cons, List.length_cons]
    rw [show 2 * (w.length + 1) + 3 = (2 * w.length + 3) + 2 by omega,
      Function.iterate_add_apply]
    have hs : iter^[2] (some (turning .take s [] (bitSym b :: List.map bitSym w) out)) =
        some (turning .take (some (bitSym b)) [] (List.map bitSym w) (b :: out)) := by
      cases b <;> rfl
    rw [hs, ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem recode_steps (N k l i : ℕ) :
    let input := encNbrIn (N,k,l,i)
    let out := directEncoding (N,k,l,i)
    iter^[3 * (binWord N).length + 2 + (3 * (binWord k).length + 2) +
          (3 * (binWord l).length + 2) + (2 * (binWord i).length + 1) +
          (2 * out.length + 3)]
      (some (start (.read .first) none input)) = some (finish (PC := PC) none out) := by
  dsimp only
  let w₁ := binWord N
  let w₂ := binWord k
  let w₃ := binWord l
  let w₄ := binWord i
  let out := packedBits w₁ ++ packedBits w₂ ++ packedBits w₃ ++ w₄
  change iter^[3*w₁.length+2 + (3*w₂.length+2) + (3*w₃.length+2) +
        (2*w₄.length+1) + (2*out.length+3)] (some (reading .first none _ [])) = _
  have hi : encNbrIn (N,k,l,i) =
      w₁.map bitSym ++ [2] ++ (w₂.map bitSym ++ [2] ++
        (w₃.map bitSym ++ [2] ++ (w₄.map bitSym ++ [2]))) := by
    simp [encNbrIn, encWords, w₁, w₂, w₃, w₄, List.append_assoc]
  rw [hi]
  rw [show 3*w₁.length+2+(3*w₂.length+2)+(3*w₃.length+2)+(2*w₄.length+1)+(2*out.length+3) =
      (2*out.length+3) + ((2*w₄.length+1) + ((3*w₃.length+2) +
        ((3*w₂.length+2) + (3*w₁.length+2)))) by omega]
  rw [Function.iterate_add_apply iter (2*out.length+3) _,
    Function.iterate_add_apply iter (2*w₄.length+1) _,
    Function.iterate_add_apply iter (3*w₃.length+2) _,
    Function.iterate_add_apply iter (3*w₂.length+2) _]
  rw [scan_early .first (by decide)]
  simp only [Field.next]
  rw [scan_early .second (by decide)]
  simp only [Field.next]
  rw [scan_early .third (by decide)]
  simp only [Field.next]
  rw [scan_last]
  have hrev : out.reverse.map bitSym = w₄.reverse.map bitSym ++
      ((packedBits w₃).reverse.map bitSym ++
        ((packedBits w₂).reverse.map bitSym ++ ((packedBits w₁).reverse.map bitSym ++ []))) := by
    simp [out, List.reverse_append, List.append_assoc]
  rw [← hrev]
  have hturn := turn out.reverse [] (some 2)
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hturn
  exact hturn

/-- Frames the first three words, and writes the last without its separator. -/
theorem neighborInput_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime encNbrIn directEncoding id) := by
  refine ⟨certify (.read .first) none code encNbrIn directEncoding id
    (7 * Polynomial.X + Polynomial.C 16) ?_⟩
  rintro ⟨N,k,l,i⟩
  let w₁ := binWord N
  let w₂ := binWord k
  let w₃ := binWord l
  let w₄ := binWord i
  let out := directEncoding (N,k,l,i)
  refine ⟨⟨_, recode_steps N k l i⟩, ?_⟩
  have hpack (w : List Bool) : (packedBits w).length = 2 * w.length + 1 := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      have hs : packedBits (b :: w) = true :: b :: packedBits w := rfl
      simp [hs, ih]
      omega
  have ho : out.length = 2*(w₁.length+w₂.length+w₃.length) + w₄.length + 3 := by
    simp [out, directEncoding, w₁, w₂, w₃, w₄, hpack]
    omega
  have hi : (encNbrIn (N,k,l,i)).length = w₁.length + w₂.length + w₃.length + w₄.length + 4 := by
    simp [encNbrIn, encWords, w₁, w₂, w₃, w₄]
    omega
  change 3*w₁.length+2 + (3*w₂.length+2) + (3*w₃.length+2) +
        (2*w₄.length+1) + (2*out.length+3) ≤ _
  simp [Polynomial.eval_add, Polynomial.eval_mul, hi]
  omega

end CNFEncComplexity.NeighborInput

namespace CNFEncComplexity

private theorem encodePosNum_eq_bits (p : PosNum) :
    Computability.encodePosNum p = (p : ℕ).bits := by
  induction p with
  | one => rfl
  | bit0 p ih =>
    rw [Computability.encodePosNum, PosNum.cast_bit0, ← two_mul,
      Nat.bit0_bits _ (Nat.ne_of_gt p.to_nat_pos), ih]
  | bit1 p ih =>
    rw [Computability.encodePosNum, PosNum.cast_bit1, ← two_mul,
      Nat.bit1_bits, ih]

/-- The published binary encoding is the canonical least-significant-first bit list. -/
theorem binWord_eq_natBits (n : ℕ) : binWord n = n.bits := by
  unfold binWord Computability.encodeNat
  conv_rhs => rw [← Num.to_of_nat n]
  generalize (n : Num) = m
  cases m with
  | zero => rfl
  | pos p => exact encodePosNum_eq_bits p

/-- Each of the four binary words is followed by one delimiter. -/
theorem encNbrIn_length (N k l i : ℕ) :
    (encNbrIn (N,k,l,i)).length = N.size + k.size + l.size + i.size + 4 := by
  simp [encNbrIn, encWords, binWord_eq_natBits, Nat.size_eq_bits_len]
  omega

/-- The normalized right label fits in `j + 2` bits, even on invalid RAM programs. -/
theorem ramFoldedLayer_output_size (P : TimeSpaceMA.Program) (e C N j l i ρ : ℕ)
    (h : ramFoldedLayer P e C (N,j,l,i) = some ρ) : ρ.size ≤ j+2 := by
  by_cases hj : j ≤ Nat.log 2 N ∧ l < N
  · unfold ramFoldedLayer at h
    dsimp only at h
    rw [if_pos hj] at h
    let n := Nat.log 2 N + 1
    let B := C + 3 * (Nat.log 2 n + 1)
    let M := (2 : ℕ)^(j+2-B)
    let u := (2 : ℕ)^(min (j+2) B)
    let st := (P.step TimeSpaceMA.zeroTape)^[n^e+e]
      (TimeSpaceMA.State.init (TimeSpaceMA.memOf [n,j,l]))
    change (if st.halted = true ∧ i / u < st.mem 0 then
      some (i % u * M + st.mem (1+i / u) % M) else none) = some ρ at h
    split at h
    · obtain rfl := Option.some.inj h
      apply Nat.size_le.mpr
      have hM : 0 < M := Nat.pow_pos (by decide)
      have hu : 0 < u := Nat.pow_pos (by decide)
      have huM : u * M = 2^(j+2) := by
        dsimp [u, M]
        rw [← pow_add]
        congr 1
        omega
      calc
        _ < i % u * M + M := Nat.add_lt_add_left (Nat.mod_lt _ hM) _
        _ = (i % u + 1) * M := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ u * M := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (Nat.mod_lt _ hu))
        _ = _ := huM
    · cases h
  · simp [ramFoldedLayer, hj] at h

/-- The Teutsch neighbor wrapper's output has at most a constant number of bits more
than its input, for every tuple and regardless of what the interpreted RAM returns. -/
theorem mergedRamNbr_output_length (P : TimeSpaceMA.Program) (e C : ℕ) (degree : ℕ → ℕ)
    (N k l i : ℕ) :
    (encOptNat (mergeNbr degree (ramFoldedLayer P e C) (N,k,l,i))).length ≤
      (encNbrIn (N,k,l,i)).length := by
  rw [encNbrIn_length]
  let j := i / degree N
  unfold mergeNbr
  change (encOptNat (if j ≤ k ∧ j ≤ Nat.log 2 N then
      (ramFoldedLayer P e C (N,j,l,i % degree N)).map ((2^(j+2)-4) + ·) else none)).length ≤ _
  split
  next hj =>
    cases h : ramFoldedLayer P e C (N,j,l,i % degree N) with
    | none => simp [encOptNat]
    | some ρ =>
      simp only [Option.map_some, encOptNat, List.length_cons, binWord_eq_natBits, Nat.size_eq_bits_len]
      have hρ := Nat.size_le.mp (ramFoldedLayer_output_size P e C N j l (i % degree N) ρ h)
      have hsize : (2^(j+2)-4 + ρ).size ≤ j+3 := by
        apply Nat.size_le.mpr
        have htwo : (2 : ℕ)^(j+3) = 2^(j+2) * 2 := pow_succ _ _
        rw [htwo]
        omega
      have hjN : j ≤ N.size := by
        by_cases hN : N = 0
        · subst N
          simpa [Nat.log_zero_right] using hj.2
        · exact (Nat.lt_size.mpr (Nat.pow_le_of_le_log hN hj.2)).le
      omega
  next _ => simp [encOptNat]

end CNFEncComplexity

namespace TimeSpaceMA

/-- The most recent write to an address is first. Missing addresses hold zero. -/
def sparseRead : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (a,v) :: rs, i => if i = a then v else sparseRead rs i

/-- Encode an initial dense input into records starting at `a`. -/
def sparseInputRecords (a : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | v :: vs => (a,v) :: sparseInputRecords (a+1) vs

@[simp] theorem sparseRead_cons (a v i : ℕ) (rs : List (ℕ × ℕ)) :
    sparseRead ((a,v) :: rs) i = (if i = a then v else sparseRead rs i) := rfl

private theorem sparseInputRecords_read_lt (a i : ℕ) (xs : List ℕ) (h : i < a) :
    sparseRead (sparseInputRecords a xs) i = 0 := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [sparseInputRecords, sparseRead_cons, if_neg (by omega)]
    exact ih (a+1) (by omega)

private theorem sparseInputRecords_read_add (a i : ℕ) (xs : List ℕ) :
    sparseRead (sparseInputRecords a xs) (a+i) = xs.getD i 0 := by
  induction xs generalizing a i with
  | nil => simp [sparseInputRecords, sparseRead]
  | cons x xs ih =>
    cases i with
    | zero => simp [sparseInputRecords]
    | succ i =>
      simp only [sparseInputRecords, sparseRead_cons, if_neg (show a+(i+1) ≠ a by omega)]
      rw [show a+(i+1) = (a+1)+i by omega]
      simpa using ih (a+1) i

@[simp] theorem sparseInputRecords_read (xs : List ℕ) :
    sparseRead (sparseInputRecords 0 xs) = memOf xs := by
  funext i
  simpa [memOf] using sparseInputRecords_read_add 0 i xs

/-- The executable RAM state, using a finite history of writes for the memory. -/
structure SparseState where
  pc : ℕ
  records : List (ℕ × ℕ)
  cursor : ℕ
  halted : Bool
  work : ℕ
  deriving Repr

/-- Initial state with input cells starting at address zero. -/
def SparseState.init (xs : List ℕ) : SparseState :=
  ⟨0, sparseInputRecords 0 xs, 0, false, 0⟩

/-- Interpret the finite write history as the reference machine's full memory. -/
def SparseState.toState (st : SparseState) : State :=
  ⟨st.pc, sparseRead st.records, st.cursor, st.halted, st.work⟩

@[simp] theorem SparseState.init_toState (xs : List ℕ) :
    (SparseState.init xs).toState = State.init (memOf xs) := by
  simp [SparseState.init, SparseState.toState, State.init]

/-- One executable sparse step, including the exact reference work charge. -/
def Program.sparseStep (p : Program) (τ : ℕ → Bool) (st : SparseState) : SparseState :=
  let read := sparseRead st.records
  if st.halted then st
  else
    match p[st.pc]? with
    | none => st
    | some (.const d c) =>
        { st with
          pc := st.pc + 1
          records := (d,c) :: st.records
          work := st.work + 1 + d.size + c.size }
    | some (.add d a b) =>
        let u := read a
        let v := read b
        { st with
          pc := st.pc + 1
          records := (d,u+v) :: st.records
          work := st.work + 1 + d.size + a.size + b.size + u.size + v.size + (u + v).size }
    | some (.monus d a b) =>
        let u := read a
        let v := read b
        { st with
          pc := st.pc + 1
          records := (d,u-v) :: st.records
          work := st.work + 1 + d.size + a.size + b.size + u.size + v.size + (u - v).size }
    | some (.load d a) =>
        let u := read a
        let v := read u
        { st with
          pc := st.pc + 1
          records := (d,v) :: st.records
          work := st.work + 1 + d.size + a.size + u.size + v.size }
    | some (.store a b) =>
        let u := read a
        let v := read b
        { st with
          pc := st.pc + 1
          records := (u,v) :: st.records
          work := st.work + 1 + a.size + b.size + u.size + v.size }
    | some (.jle a b target) =>
        let u := read a
        let v := read b
        { st with
          pc := if u ≤ v then target else st.pc + 1
          work := st.work + 1 + a.size + b.size + u.size + v.size + target.size }
    | some (.coin d) =>
        let v := (τ st.cursor).toNat
        { st with
          pc := st.pc + 1
          records := (d,v) :: st.records
          cursor := st.cursor + 1
          work := st.work + 1 + d.size + v.size }
    | some .halt =>
        { st with
          halted := true
          work := st.work + 1 }

private theorem sparseRead_push_eq_update (a v : ℕ) (rs : List (ℕ × ℕ)) :
    sparseRead ((a,v) :: rs) = Function.update (sparseRead rs) a v := by
  funext i
  simp [Function.update_apply]

/-- A sparse step is exactly one reference RAM step on the decoded state. -/
theorem Program.sparseStep_toState (P : Program) (τ : ℕ → Bool) (st : SparseState) :
    (P.sparseStep τ st).toState = P.step τ st.toState := by
  by_cases h : st.halted = true
  · simp [Program.sparseStep, Program.step, SparseState.toState, h]
  · cases hi : P[st.pc]? with
    | none => simp [Program.sparseStep, Program.step, SparseState.toState, h, hi]
    | some ins =>
      cases ins <;> simp only [Program.sparseStep, Program.step, SparseState.toState,
        h, hi, if_false, Bool.false_eq_true, sparseRead_push_eq_update]

/-- Run an executable bounded simulation, including when the machine never halts. -/
def Program.sparseRun (P : Program) (τ : ℕ → Bool) (xs : List ℕ) (fuel : ℕ) : SparseState :=
  (P.sparseStep τ)^[fuel] (SparseState.init xs)

/-- The executable bounded simulation agrees with reference iteration on all inputs. -/
theorem Program.sparseRun_toState (P : Program) (τ : ℕ → Bool) (xs : List ℕ) (fuel : ℕ) :
    (P.sparseRun τ xs fuel).toState = (P.step τ)^[fuel] (State.init (memOf xs)) := by
  induction fuel with
  | zero => simp [Program.sparseRun]
  | succ fuel ih =>
    unfold Program.sparseRun at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', P.sparseStep_toState, ih]

@[simp] theorem sparseInputRecords_length (a : ℕ) (xs : List ℕ) :
    (sparseInputRecords a xs).length = xs.length := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [sparseInputRecords, ih]

/-- A sparse step appends at most one record regardless of instruction or control flow. -/
theorem Program.sparseStep_records_le (P : Program) (τ : ℕ → Bool) (st : SparseState) :
    (P.sparseStep τ st).records.length ≤ st.records.length + 1 := by
  by_cases hh : st.halted = true
  · simp [Program.sparseStep, hh, Nat.le_succ]
  · cases hi : P[st.pc]? with
    | none => simp [Program.sparseStep, hh, hi, Nat.le_succ]
    | some ins =>
      cases ins <;> simp [Program.sparseStep, hh, hi, Nat.le_succ]

/-- At most one write record is added per iteration. -/
theorem Program.sparseRun_records_le (P : Program) (τ : ℕ → Bool) (xs : List ℕ) (fuel : ℕ) :
    (P.sparseRun τ xs fuel).records.length ≤ xs.length + fuel := by
  induction fuel with
  | zero => simp [Program.sparseRun, SparseState.init]
  | succ fuel ih =>
    unfold Program.sparseRun at ih ⊢
    rw [Function.iterate_succ_apply']
    exact Nat.le_trans (P.sparseStep_records_le τ _) (Nat.add_le_add_right ih 1)

/-- The fixed numeric operands of an instruction. All indirect addresses are read from memory. -/
def Instr.operands : Instr → List ℕ
  | .const d c => [d,c]
  | .add d a b | .monus d a b => [d,a,b]
  | .load d a | .store d a => [d,a]
  | .jle a b t => [a,b,t]
  | .coin d => [d]
  | .halt => []

/-- A bound on the bit widths of all fixed operands in the program. -/
def Program.operandWidth (P : Program) : ℕ :=
  (P.flatMap Instr.operands).foldl (fun b n => max b n.size) 1

private theorem size_le_foldl_max (xs : List ℕ) (acc : ℕ) :
    (acc ≤ xs.foldl (fun b n => max b n.size) acc) ∧
    ∀ x ∈ xs, x.size ≤ xs.foldl (fun b n => max b n.size) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hstart, hall⟩ := ih (max acc x.size)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) hstart, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Nat.le_trans (Nat.le_max_right _ _) hstart
    · exact hall y hy

/-- Every literal address, target, and constant fits the fixed program width. -/
theorem Program.operand_size_le {P : Program} {ins : Instr} {n : ℕ}
    (hins : ins ∈ P) (hn : n ∈ ins.operands) : n.size ≤ P.operandWidth :=
  (size_le_foldl_max _ 1).2 n (List.mem_flatMap.mpr ⟨ins, hins, hn⟩)

/-- Looking up an address cannot produce a value wider than the stored records. -/
theorem sparseRead_size_le (rs : List (ℕ × ℕ)) (B : ℕ)
    (hwidth : ∀ r ∈ rs, r.2.size ≤ B) (i : ℕ) : (sparseRead rs i).size ≤ B := by
  induction rs with
  | nil => simp [sparseRead]
  | cons r rs ih =>
    obtain ⟨a,v⟩ := r
    rw [sparseRead_cons]
    split
    · exact hwidth (a,v) (List.mem_cons_self)
    · exact ih (fun r hr => hwidth r (List.mem_cons_of_mem _ hr))

private theorem size_add_le_succ {x y B : ℕ} (hx : x.size ≤ B) (hy : y.size ≤ B) :
    (x+y).size ≤ B+1 := by
  have hx' := Nat.size_le.mp hx
  have hy' := Nat.size_le.mp hy
  apply Nat.size_le.mpr
  rw [Nat.pow_succ]
  omega

private theorem size_inc_le_succ {x B : ℕ} (hx : x.size ≤ B) (hB : 0 < B) :
    (x+1).size ≤ B+1 :=
  size_add_le_succ hx (by simpa using (show 1 ≤ B from hB))

/-- A bit-width invariant for the finite-list configuration and both control counters. -/
def SparseState.WidthLE (st : SparseState) (B : ℕ) : Prop :=
  st.pc.size ≤ B ∧ st.cursor.size ≤ B ∧
  ∀ r ∈ st.records, r.1.size ≤ B ∧ r.2.size ≤ B

theorem SparseState.WidthLE.mono {st : SparseState} {A B : ℕ}
    (h : st.WidthLE A) (hab : A ≤ B) : st.WidthLE B :=
  ⟨Nat.le_trans h.1 hab, Nat.le_trans h.2.1 hab, fun r hr =>
    ⟨Nat.le_trans (h.2.2 r hr).1 hab, Nat.le_trans (h.2.2 r hr).2 hab⟩⟩

/-- A step can increase address, data, program-counter and cursor widths by at most one bit. -/
theorem Program.sparseStep_width_le (P : Program) (τ : ℕ → Bool) (st : SparseState) (B : ℕ)
    (hB : 0 < B) (hP : P.operandWidth ≤ B) (h : st.WidthLE B) :
    (P.sparseStep τ st).WidthLE (B+1) := by
  have hkeep := h.mono (Nat.le_succ B)
  have hread (i : ℕ) : (sparseRead st.records i).size ≤ B :=
    sparseRead_size_le st.records B (fun r hr => (h.2.2 r hr).2) i
  have hpc : (st.pc+1).size ≤ B+1 := size_inc_le_succ h.1 hB
  have hcur : (st.cursor+1).size ≤ B+1 := size_inc_le_succ h.2.1 hB
  have hcons (d v : ℕ) (hd : d.size ≤ B+1) (hv : v.size ≤ B+1) :
      ∀ r ∈ (d,v) :: st.records, r.1.size ≤ B+1 ∧ r.2.size ≤ B+1 := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨hd, hv⟩
    · exact hkeep.2.2 r hr
  by_cases hh : st.halted = true
  · simpa [Program.sparseStep, hh] using hkeep
  cases hi : P[st.pc]? with
  | none => simpa [Program.sparseStep, hh, hi] using hkeep
  | some ins =>
    have hop (n : ℕ) (hn : n ∈ ins.operands) : n.size ≤ B+1 :=
      Nat.le_trans (P.operand_size_le (List.mem_of_getElem? hi) hn) (Nat.le_trans hP (Nat.le_succ _))
    cases ins with
    | const d c =>
      simp only [Program.sparseStep, hh, hi, if_false, Bool.false_eq_true, SparseState.WidthLE]
      exact ⟨hpc, hkeep.2.1, hcons d c (hop d (by simp [Instr.operands]))
        (hop c (by simp [Instr.operands]))⟩
    | add d a b =>
      simp only [Program.sparseStep, hh, hi, if_false, Bool.false_eq_true, SparseState.WidthLE]
      exact ⟨hpc, hkeep.2.1, hcons d _ (hop d (by simp [Instr.operands]))
        (size_add_le_succ (hread a) (hread b))⟩
    | monus d a b =>
      simp only [Program.sparseStep, hh, hi, if_false, Bool.false_eq_true, SparseState.WidthLE]
      exact ⟨hpc, hkeep.2.1, hcons d _ (hop d (by simp [Instr.operands]))
        (Nat.le_trans (Nat.size_le_size (Nat.sub_le _ _)) (Nat.le_trans (hread a) (Nat.le_succ _)))⟩
    | load d a =>
      simp only [Program.sparseStep, hh, hi, if_false, Bool.false_eq_true, SparseState.WidthLE]
      exact ⟨hpc, hkeep.2.1, hcons d _ (hop d (by simp [Instr.operands]))
        (Nat.le_trans (hread _) (Nat.le_succ _))⟩
    | store a b =>
      simp only [Program.sparseStep, hh, hi, if_false, Bool.false_eq_true, SparseState.WidthLE]
      exact ⟨hpc, hkeep.2.1, hcons _ _ (Nat.le_trans (hread a) (Nat.le_succ _))
        (Nat.le_trans (hread b) (Nat.le_succ _))⟩
    | jle a b target =>
      simp only [Program.sparseStep, hh, hi, if_false, Bool.false_eq_true, SparseState.WidthLE]
      refine ⟨?_, hkeep.2⟩
      split
      · exact hop target (by simp [Instr.operands])
      · exact hpc
    | coin d =>
      simp only [Program.sparseStep, hh, hi, if_false, Bool.false_eq_true, SparseState.WidthLE]
      have hbool : ((τ st.cursor).toNat).size ≤ 1 := by cases τ st.cursor <;> decide
      exact ⟨hpc, hcur, hcons d _ (hop d (by simp [Instr.operands])) (by omega)⟩
    | halt =>
      simpa [Program.sparseStep, hh, hi, SparseState.WidthLE] using hkeep

private theorem sparseInputRecords_mem_bounds (a : ℕ) (xs : List ℕ) (r : ℕ × ℕ)
    (hr : r ∈ sparseInputRecords a xs) : r.1 < a + xs.length ∧ r.2 ∈ xs := by
  induction xs generalizing a with
  | nil => simp [sparseInputRecords] at hr
  | cons x xs ih =>
    rw [sparseInputRecords] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    · obtain ⟨haddr, hval⟩ := ih (a+1) hr
      exact ⟨by simp; omega, List.mem_cons_of_mem _ hval⟩

/-- All fields of a finite run's memory records and control counters remain short, even if
it runs out of fuel or becomes stuck. The bound is linear in fuel plus input width. -/
theorem Program.sparseRun_width_le (P : Program) (τ : ℕ → Bool)
    (xs : List ℕ) (fuel B : ℕ) (hB : 0 < B) (hP : P.operandWidth ≤ B)
    (hlen : xs.length ≤ 2^B) (hdata : ∀ x ∈ xs, x.size ≤ B) :
    (P.sparseRun τ xs fuel).WidthLE (B+fuel) := by
  induction fuel with
  | zero =>
    simp only [Program.sparseRun, Function.iterate_zero, id_eq, Nat.add_zero]
    refine ⟨by simp [SparseState.init], by simp [SparseState.init], ?_⟩
    intro r hr
    obtain ⟨haddr,hval⟩ := sparseInputRecords_mem_bounds 0 xs r hr
    refine ⟨Nat.size_le.mpr (Nat.lt_of_lt_of_le ?_ hlen), hdata _ hval⟩
    simpa using haddr
  | succ fuel ih =>
    unfold Program.sparseRun at ih ⊢
    rw [Function.iterate_succ_apply']
    exact P.sparseStep_width_le τ _ (B+fuel) (by omega) (by omega) ih

end TimeSpaceMA

namespace TimeSpaceMA

abbrev ShortState := ℕ × Bool × List (ℕ × ℕ)

/-- State fields observed by deterministic neighbor evaluators. -/
def SparseState.toShort (st : SparseState) : ShortState := (st.pc, st.halted, st.records)

/-- An executable action for one fixed instruction. The zero coin tape is implicit. -/
def shortAction (ins : Instr) (s : ShortState) : ShortState :=
  let m := s.2.2
  let read := sparseRead m
  let pc := s.1 + 1
  match ins with
  | .const d c => (pc, false, (d,c) :: m)
  | .add d a b => (pc, false, (d,read a + read b) :: m)
  | .monus d a b => (pc, false, (d,read a - read b) :: m)
  | .load d a => (pc, false, (d,read (read a)) :: m)
  | .store a b => (pc, false, (read a,read b) :: m)
  | .jle a b target => (if read a ≤ read b then target else pc, false, m)
  | .coin d => (pc, false, (d,0) :: m)
  | .halt => (s.1, true, m)

/-- Dispatch by bounded program code. The final case is the stuck state. -/
def shortDispatch (s : ShortState) : ℕ → Program → ShortState
  | _, [] => s
  | base, ins::tail => if s.1 = base then shortAction ins s else shortDispatch s (base+1) tail

/-- Halted configurations remain fixed; otherwise use the instruction selected by the PC. -/
def shortStep (P : Program) (s : ShortState) : ShortState :=
  if s.2.1 then s else shortDispatch s 0 P

private theorem shortDispatch_correct (s : ShortState) (base : ℕ) (P : Program) :
    shortDispatch s base P =
      if base ≤ s.1 then (P[s.1-base]?).elim s (fun ins => shortAction ins s) else s := by
  induction P generalizing base with
  | nil => simp [shortDispatch]
  | cons ins tail ih =>
    by_cases h : s.1 = base
    · simp [shortDispatch, h]
    · rw [shortDispatch, if_neg h, ih]
      by_cases hlt : base ≤ s.1
      · have hlt' : base + 1 ≤ s.1 := by omega
        rw [if_pos hlt, if_pos hlt', show s.1-base = (s.1-(base+1))+1 by omega]
        rfl
      · have hlt' : ¬ base + 1 ≤ s.1 := by omega
        rw [if_neg hlt, if_neg hlt']

/-- The work-free state is an exact quotient of the sparse simulation on a zero tape. -/
theorem shortStep_correct (P : Program) (st : SparseState) :
    shortStep P st.toShort = (P.sparseStep zeroTape st).toShort := by
  by_cases h : st.halted = true
  · simp [shortStep, SparseState.toShort, Program.sparseStep, h]
  · rw [shortStep]
    simp only [SparseState.toShort, h, Bool.false_eq_true, if_false]
    rw [shortDispatch_correct]
    simp only [Nat.zero_le, if_true, Nat.sub_zero]
    cases hi : P[st.pc]? with
    | none => simp [Program.sparseStep, hi, h]
    | some ins => cases ins <;> simp [Program.sparseStep, hi, h, shortAction, zeroTape]

/-- The three input cells of the disperser program are loaded before simulation. -/
def shortInit (x : ℕ × ℕ × ℕ × ℕ) : ShortState :=
  (0, false, [(0,x.1), (1,x.2.1), (2,x.2.2.1)])

/-- Interpret the RAM program using the indicated number of steps. -/
def shortRun (P : Program) (x : ℕ × ℕ × ℕ × ℕ) : ShortState :=
  (shortStep P)^[x.2.2.2] (shortInit x)

/-- Work-free iteration agrees with sparse RAM iteration for every prefix. -/
theorem shortIterate_correct (P : Program) (n j l t : ℕ) :
    (shortStep P)^[t] (shortInit (n,j,l,0)) = (P.sparseRun zeroTape [n,j,l] t).toShort := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold Program.sparseRun at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, shortStep_correct]

/-- The halted flag and decoded memory agree with the published functional RAM. -/
theorem shortRun_correct (P : Program) (n j l t : ℕ) :
    let st := (P.step zeroTape)^[t] (State.init (memOf [n,j,l]))
    (shortRun P (n,j,l,t)).2.1 = st.halted ∧
    sparseRead (shortRun P (n,j,l,t)).2.2 = st.mem := by
  unfold shortRun
  change (let st := (P.step zeroTape)^[t] (State.init (memOf [n,j,l])); _)
  have h0 : shortInit (n,j,l,t) = shortInit (n,j,l,0) := rfl
  dsimp only
  rw [h0, shortIterate_correct]
  have h := P.sparseRun_toState zeroTape [n,j,l] t
  rw [← h]
  exact ⟨rfl, rfl⟩

end TimeSpaceMA

namespace TimeSpaceMA

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev encRecord : (ℕ × ℕ) ↪ List Bool := encPair encNat encNat
abbrev encRecords : List (ℕ × ℕ) ↪ List Bool := encList encRecord
abbrev encShortState : ShortState ↪ List Bool := encPair encNat (encPair encBool encRecords)
abbrev encShortInput : (ℕ × ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encUnary))

private theorem sparseRead_eq_find (rs : List (ℕ × ℕ)) (i : ℕ) :
    sparseRead rs i = ((rs.find? fun r => decide (i = r.1)).getD (0,0)).2 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨a,v⟩ := r
    by_cases h : i = a <;> simp [List.find?, h, ih]

/-- Sparse lookup uses a linear scan of records with binary key comparison. -/
theorem sparseRead_polytime :
    ComputableTidilyInPolyTime (fun p : List (ℕ × ℕ) × ℕ => sparseRead p.1 p.2)
      (encPair encRecords encNat) encNat := by
  simp only [sparseRead_eq_find]
  have htest : ComputableTidilyInPolyTime
      (fun p : ℕ × (ℕ × ℕ) => decide (p.1 = p.2.1)) (encPair encNat encRecord) encBool :=
    decide_eq' (fst encNat encRecord) ((fst encNat encNat).comp (snd encNat encRecord))
  have hfind := findWith htest (snd encRecords encNat) (fst encRecords encNat)
  exact (optionGetDWithInput hfind (const (0,0))).snd'

private theorem shortRecords_polytime :
    ComputableTidilyInPolyTime (fun s : ShortState => s.2.2) encShortState encRecords :=
  (snd encBool encRecords).comp (snd encNat (encPair encBool encRecords))

private theorem shortHalted_polytime :
    ComputableTidilyInPolyTime (fun s : ShortState => s.2.1) encShortState encBool :=
  (fst encBool encRecords).comp (snd encNat (encPair encBool encRecords))

private theorem shortPC_polytime :
    ComputableTidilyInPolyTime (fun s : ShortState => s.1) encShortState encNat :=
  fst encNat (encPair encBool encRecords)

private theorem shortRead_pc_polytime {addr : ShortState → ℕ}
    (ha : ComputableTidilyInPolyTime addr encShortState encNat) :
    ComputableTidilyInPolyTime (fun s : ShortState => sparseRead s.2.2 (addr s))
      encShortState encNat :=
  sparseRead_polytime.comp (shortRecords_polytime.prod ha)

private theorem shortRead_fixed_polytime (a : ℕ) :
    ComputableTidilyInPolyTime (fun s : ShortState => sparseRead s.2.2 a)
      encShortState encNat :=
  shortRead_pc_polytime (const a)

private theorem shortPCSucc_polytime :
    ComputableTidilyInPolyTime (fun s : ShortState => s.1+1) encShortState encNat :=
  binary_add' shortPC_polytime (const 1)

private theorem shortWrite_polytime {addr val : ShortState → ℕ}
    (ha : ComputableTidilyInPolyTime addr encShortState encNat)
    (hv : ComputableTidilyInPolyTime val encShortState encNat) :
    ComputableTidilyInPolyTime (fun s : ShortState => (s.1+1, false, (addr s,val s)::s.2.2))
      encShortState encShortState :=
  shortPCSucc_polytime.prod ((const false).prod (cons' (ha.prod hv) shortRecords_polytime))

private theorem shortAction_polytime (ins : Instr) :
    ComputableTidilyInPolyTime (shortAction ins) encShortState encShortState := by
  cases ins with
  | const d c => exact shortWrite_polytime (const d) (const c)
  | add d a b =>
    exact shortWrite_polytime (const d)
      (binary_add' (shortRead_fixed_polytime a) (shortRead_fixed_polytime b))
  | monus d a b =>
    exact shortWrite_polytime (const d)
      (binary_sub' (shortRead_fixed_polytime a) (shortRead_fixed_polytime b))
  | load d a => exact shortWrite_polytime (const d) (shortRead_pc_polytime (shortRead_fixed_polytime a))
  | store a b => exact shortWrite_polytime (shortRead_fixed_polytime a) (shortRead_fixed_polytime b)
  | jle a b target =>
    exact (ite_decide (binary_le' (shortRead_fixed_polytime a) (shortRead_fixed_polytime b))
      (const target) shortPCSucc_polytime).prod ((const false).prod shortRecords_polytime)
  | coin d => exact shortWrite_polytime (const d) (const 0)
  | halt => exact shortPC_polytime.prod ((const true).prod shortRecords_polytime)

private theorem shortDispatch_polytime (P : Program) (base : ℕ) :
    ComputableTidilyInPolyTime (fun s => shortDispatch s base P) encShortState encShortState := by
  induction P generalizing base with
  | nil => exact id'
  | cons ins P ih =>
    exact ite_decide (decide_eq' shortPC_polytime (const base)) (shortAction_polytime ins) (ih (base+1))

private theorem shortStep_polytime (P : Program) :
    ComputableTidilyInPolyTime (shortStep P) encShortState encShortState :=
  shortHalted_polytime.cond id' (shortDispatch_polytime P 0)

private theorem shortInit_polytime :
    ComputableTidilyInPolyTime shortInit encShortInput encShortState := by
  let tail := encPair encNat (encPair encNat encUnary)
  have hn : ComputableTidilyInPolyTime (fun x : ℕ × ℕ × ℕ × ℕ => x.1) encShortInput encNat :=
    fst encNat tail
  have ht := snd encNat tail
  have hj := (fst encNat (encPair encNat encUnary)).comp ht
  have hl := (fst encNat encUnary).comp ((snd encNat (encPair encNat encUnary)).comp ht)
  exact (const 0).prod ((const false).prod (cons' ((const 0).prod hn)
    (cons' ((const 1).prod hj) (cons' ((const 2).prod hl) (const [])))))

private theorem shortFuel_polytime :
    ComputableTidilyInPolyTime (fun x : ℕ × ℕ × ℕ × ℕ => x.2.2.2) encShortInput encUnary :=
  (snd encNat encUnary).comp ((snd encNat (encPair encNat encUnary)).comp
      (snd encNat (encPair encNat (encPair encNat encUnary))))

private theorem shortState_length_le {st : SparseState} {B r : ℕ}
    (hw : st.WidthLE B) (hr : st.records.length ≤ r) :
    (encShortState st.toShort).length ≤ 2*B + 4 + r*(6*B+3) := by
  change (encPair encNat (encPair encBool encRecords) st.toShort).length ≤ _
  simp only [SparseState.toShort, length_encPair, encNat_apply, Nat.size_eq_bits_len,
    encBool_apply, List.length_singleton]
  have hpc := hw.1
  have hrec := length_encList_le encRecord st.records (b := 3*B+1) (fun p hp => by
    have h := hw.2.2 p hp
    simp only [encRecord, length_encPair, encNat_apply, Nat.size_eq_bits_len]
    omega)
  have hmul : st.records.length*(6*B+3) ≤ r*(6*B+3) := Nat.mul_le_mul_right _ hr
  have ht : (encRecords st.records).length ≤ st.records.length*(6*B+3) := by
    simpa only [show 2*(3*B+1)+1 = 6*B+3 by omega] using hrec
  omega

/-- A fixed finite RAM program can be evaluated for an input number of unary steps in polynomial
 time, including stuck and nonhalting runs. -/
theorem shortRun_polytime (P : Program) :
    ComputableTidilyInPolyTime (shortRun P) encShortInput encShortState := by
  let W := P.operandWidth + 2
  let size := fun x : ℕ × ℕ × ℕ × ℕ => (encShortInput x).length
  let width := fun x : ℕ × ℕ × ℕ × ℕ => W + 2 * size x
  let records := fun x : ℕ × ℕ × ℕ × ℕ => 3 + size x
  let bound := fun x => 2*width x + 4 + records x*(6*width x+3)
  have hsize : PolyBounded size size := .self
  have hw : PolyBounded size width := (PolyBounded.const W).add ((PolyBounded.const 2).mul hsize)
  have hr : PolyBounded size records := (PolyBounded.const 3).add hsize
  have hb : PolyBounded size bound :=
    (((PolyBounded.const 2).mul hw).add (PolyBounded.const 4)).add (hr.mul (((PolyBounded.const 6).mul hw).add (PolyBounded.const 3)))
  unfold shortRun
  apply iterate shortFuel_polytime shortInit_polytime (shortStep_polytime P) hb
  rintro ⟨n,j,l,t⟩ i hi
  have hi' : i ≤ t := hi
  have hlen : size (n,j,l,t) = 2*n.size + 1 + (2*j.size + 1 + (2*l.size + 1 + t)) := by
    simp [size, encShortInput, encNat_apply, Nat.size_eq_bits_len, encUnary_apply,
      Nat.add_assoc]
  change (encShortState ((shortStep P)^[i] (shortInit (n,j,l,t)))).length ≤ bound (n,j,l,t)
  rw [show shortInit (n,j,l,t) = shortInit (n,j,l,0) by rfl, shortIterate_correct]
  let B := W + size (n,j,l,t)
  have hB : 0 < B := by dsimp [B,W]; omega
  have hfixed : P.operandWidth ≤ B := by dsimp [B,W]; omega
  have hsmall : [n,j,l].length ≤ 2^B := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ B by dsimp [B,W]; omega)
    simp
    omega
  have hin : ∀ x ∈ [n,j,l], x.size ≤ B := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> dsimp [B] <;> omega
  have hwidth := P.sparseRun_width_le zeroTape [n,j,l] i B hB hfixed hsmall hin
  have hcount := P.sparseRun_records_le zeroTape [n,j,l] i
  apply shortState_length_le
  · apply hwidth.mono
    dsimp [B,width]
    omega
  · dsimp [records]
    simp at hcount
    omega

end TimeSpaceMA

namespace CNFEncComplexity

open Turing.MultiTapeTM TimeSpaceMA
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

private abbrev Query := ℕ × ℕ × ℕ × ℕ
private abbrev encQuery : Query ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))
private abbrev encClockQuery : Query ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encUnary))
private abbrev encRecords := encList (encPair encNat encNat)
private abbrev encResult := encPair encNat (encPair encBool encRecords)

private theorem binaryLog : ComputableTidilyInPolyTime (Nat.log 2) encNat encUnary := by
  have heq (n : ℕ) : n.size - 1 = Nat.log 2 n := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · have hs := Nat.size_pos.mpr hn
      symm
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · exact Nat.lt_size.mp (by omega)
      · simpa only [Nat.sub_add_cancel hs] using Nat.lt_size_self n
  simpa only [Function.comp_def, heq] using
    unary_sub.comp (ComputableInPolyTime.binary_size.tidy.prod (const 1))

theorem teutschNbr_tidy (P : Program) (e C a : ℕ)
    (hRun : ComputableTidilyInPolyTime (shortRun P) encClockQuery encResult)
    (hRead : ComputableTidilyInPolyTime (fun p : List (ℕ × ℕ) × ℕ => sparseRead p.1 p.2)
      (encPair encRecords encNat) encNat) :
    ComputableTidilyInPolyTime
      (fun x => match mergeNbr (fun N => a * (Nat.log 2 N + 1)^a)
          (ramFoldedLayer P e C) x with
        | none => [false]
        | some label => true :: label.bits)
      encQuery encBits := by
  let N := fun x : Query => x.1
  let k := fun x : Query => x.2.1
  let l := fun x : Query => x.2.2.1
  let i := fun x : Query => x.2.2.2
  have hN : ComputableTidilyInPolyTime N encQuery encNat := fst _ _
  have hk : ComputableTidilyInPolyTime k encQuery encNat := (snd _ _).fst'
  have hl : ComputableTidilyInPolyTime l encQuery encNat := (snd _ _).snd'.fst'
  have hi : ComputableTidilyInPolyTime i encQuery encNat := (snd _ _).snd'.snd'
  let logN := fun x => Nat.log 2 (N x)
  have hLogU : ComputableTidilyInPolyTime logN encQuery encUnary :=
    binaryLog.comp hN
  have hLog : ComputableTidilyInPolyTime logN encQuery encNat :=
    unary_to_binary.comp hLogU
  let n := fun x => logN x + 1
  have hnu : ComputableTidilyInPolyTime n encQuery encUnary :=
    unary_add.comp (hLogU.prod (const 1))
  have hn : ComputableTidilyInPolyTime n encQuery encNat := unary_to_binary.comp hnu
  let degree := fun x => a * n x ^ a
  have hdegree : ComputableTidilyInPolyTime degree encQuery encNat :=
    binary_mul' (const a) (binary_pow' hn (const a))
  let j := fun x => i x / degree x
  let slot := fun x => i x % degree x
  have hj : ComputableTidilyInPolyTime j encQuery encNat := binary_div' hi hdegree
  have hslot : ComputableTidilyInPolyTime slot encQuery encNat := binary_mod' hi hdegree
  let smallj := fun x => min (logN x) (j x)
  have hsmallju : ComputableTidilyInPolyTime smallj encQuery encUnary :=
    (ComputableInPolyTime.binary_min_unary' hLogU.computableInPolyTime
      hj.computableInPolyTime).tidy
  let level := fun x => smallj x + 2
  have hlevel : ComputableTidilyInPolyTime level encQuery encUnary :=
    unary_add.comp (hsmallju.prod (const 2))
  let logn := fun x => Nat.log 2 (n x)
  have hlognu : ComputableTidilyInPolyTime logn encQuery encUnary :=
    binaryLog.comp hn
  let B := fun x => C + 3 * (logn x + 1)
  have hB : ComputableTidilyInPolyTime B encQuery encUnary :=
    unary_add.comp ((const C).prod
      (unary_mul.comp ((const 3).prod (unary_add.comp (hlognu.prod (const 1))))))
  let M := fun x => (2 : ℕ)^(level x - B x)
  have hM : ComputableTidilyInPolyTime M encQuery encNat :=
    binary_two_pow.comp (unary_sub.comp (hlevel.prod hB))
  let u := fun x => (2 : ℕ)^(min (level x) (B x))
  have hu : ComputableTidilyInPolyTime u encQuery encNat :=
    binary_two_pow.comp (unary_min.comp (hlevel.prod hB))
  let t := fun x => n x ^ e + e
  have ht : ComputableTidilyInPolyTime t encQuery encUnary :=
    unary_add.comp (((unary_pow e).comp hnu).prod (const e))
  let state := fun x => shortRun P (n x, j x, l x, t x)
  have hstate : ComputableTidilyInPolyTime state encQuery encResult :=
    hRun.comp (hn.prod (hj.prod (hl.prod ht)))
  let halted := fun x => (state x).2.1
  let records := fun x => (state x).2.2
  have hhalted : ComputableTidilyInPolyTime halted encQuery encBool := hstate.snd'.fst'
  have hrecords : ComputableTidilyInPolyTime records encQuery encRecords := hstate.snd'.snd'
  let quotient := fun x => slot x / u x
  have hquotient : ComputableTidilyInPolyTime quotient encQuery encNat := binary_div' hslot hu
  let count := fun x => sparseRead (records x) 0
  have hcount : ComputableTidilyInPolyTime count encQuery encNat :=
    hRead.comp (hrecords.prod (const 0))
  let valid := fun x => j x ≤ k x ∧ j x ≤ logN x ∧ l x < N x
  have hvalid : ComputableTidilyInPolyTime (fun x => decide (valid x)) encQuery encBool :=
    decide_and (binary_le' hj hk) (decide_and (binary_le' hj hLog) (binary_lt' hl hN))
  let hasEntry := fun x => halted x = true ∧ quotient x < count x
  have hentry : ComputableTidilyInPolyTime (fun x => decide (hasEntry x)) encQuery encBool :=
    decide_and (by simpa using hhalted) (binary_lt' hquotient hcount)
  let label := fun x => sparseRead (records x) (1 + quotient x)
  have hlabel : ComputableTidilyInPolyTime label encQuery encNat :=
    hRead.comp (hrecords.prod (binary_add' (const 1) hquotient))
  let folded := fun x => slot x % u x * M x + label x % M x
  have hfolded : ComputableTidilyInPolyTime folded encQuery encNat :=
    binary_add' (binary_mul' (binary_mod' hslot hu) hM) (binary_mod' hlabel hM)
  let translated := fun x => (2 ^ level x - 4) + folded x
  have htranslated : ComputableTidilyInPolyTime translated encQuery encNat :=
    binary_add' (binary_sub' (binary_two_pow.comp hlevel) (const 4)) hfolded
  have hyes : ComputableTidilyInPolyTime (fun x => true :: (translated x).bits) encQuery encBits :=
    bitsCons (const true) (natBits.comp htranslated)
  let no := fun _ : Query => [false]
  have hno : ComputableTidilyInPolyTime no encQuery encBits := const _
  refine (hvalid.ite_decide (hentry.ite_decide hyes hno) hno).of_enc_eq ?_
  intro x
  obtain ⟨N₀,k₀,l₀,i₀⟩ := x
  have hr := shortRun_correct P (n (N₀,k₀,l₀,i₀)) (j (N₀,k₀,l₀,i₀))
    (l (N₀,k₀,l₀,i₀)) (t (N₀,k₀,l₀,i₀))
  by_cases houter : j (N₀,k₀,l₀,i₀) ≤ k₀ ∧ j (N₀,k₀,l₀,i₀) ≤ Nat.log 2 N₀
  · by_cases hleft : l₀ < N₀
    · have hmin : smallj (N₀,k₀,l₀,i₀) = j (N₀,k₀,l₀,i₀) :=
        min_eq_right houter.2
      simp [encBits, mergeNbr, ramFoldedLayer, houter, hleft, valid, hasEntry,
        hr.1, hr.2, state, halted, count, records, label, translated, folded,
        slot, quotient, M, u, B, logn, level, hmin, n, logN, N, k, l, i, degree, j, t, no]
      suffices ∀ (q : Prop) [Decidable q] (z : ℕ),
          (match (if q then some z else none) with
            | none => [false]
            | some w => true :: w.bits) = (if q then true :: z.bits else [false]) by
        exact this _ _
      intro q _ z
      by_cases hq : q <;> simp [hq]
    · simp [encBits, mergeNbr, ramFoldedLayer, houter, hleft, valid, no,
        j, degree, n, logN, N, k, l, i]
  · have hvalidFalse : ¬ valid (N₀,k₀,l₀,i₀) := fun h => houter ⟨h.1, h.2.1⟩
    rw [if_neg hvalidFalse]
    simp [encBits, mergeNbr, houter, no, j, degree, n, logN, N, i]

end CNFEncComplexity

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

/-!
Time-only adaptation of the Apache-2.0 Complexitylib reverse TM2 compiler by Erik Demaine.
Source: https://github.com/cslib-community/cslib-frontier/tree/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/TM2/Reverse
This file uses the archived Prove2Me native model and packaging lemmas. It drops the space
transfer, proves the needed auxiliary storage bound directly from the zipper steps, and
uses a Mathlib natural-coefficient polynomial for the final clock.
License: https://www.apache.org/licenses/LICENSE-2.0
-/


namespace Turing.TM2

/-- Execute one source step, keeping the last configuration after halting. -/
def stepTotal {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) (cfg : Cfg Γ Λ σ) : Cfg Γ Λ σ :=
  cfg.l.elim cfg (fun l => stepAux (M l) cfg.var cfg.stk)

end Turing.TM2
/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# A bounded input zipper for the TM2 compiler

The left stack is reversed and the right stack includes the symbol under the head. A separate
flag distinguishes the left boundary from the first input symbol. An empty right stack with
the flag unset represents the right boundary, including the initial position on empty input.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.Input`: the two stacks and the left-boundary flag.
* `Turing.MultiTapeTM.ToTM2.Input.Represents`: agreement with a native input and head position.

## Main results

* `Turing.MultiTapeTM.ToTM2.Input.represents_init`: initialization represents native position one.
* `Turing.MultiTapeTM.ToTM2.Input.Represents.read_eq_inputSymbol`: reads agree with native reads.
* `Turing.MultiTapeTM.ToTM2.Input.Represents.move`: moves agree, including boundary clamping.
-/


namespace Turing.MultiTapeTM.ToTM2

/-- A read-only input tape represented by two stacks and a left-boundary flag. -/
@[ext]
structure Input (Symbol : Type) where
  /-- Input symbols strictly to the left of the head, in reverse order. -/
  left : List Symbol
  /-- Input symbols from the head onward, in input order. -/
  right : List Symbol
  /-- Whether the head is at the blank before the input. -/
  atLeft : Bool
deriving Inhabited

namespace Input

variable {Symbol : Type}

/-- Start at native position one, also when the input is empty. -/
def init (input : List Symbol) : Input Symbol := ⟨[], input, false⟩

/-- Read the current input symbol, or a blank at either boundary. -/
def read (z : Input Symbol) : Option Symbol :=
  if z.atLeft then none else z.right.head?

/-- Move left, stopping at the blank before the input. -/
def moveLeft (z : Input Symbol) : Input Symbol :=
  if z.atLeft then z else
    match z.left with
    | [] => { z with atLeft := true }
    | a :: l => ⟨l, a :: z.right, false⟩

/-- Move right, stopping at the blank after the input. -/
def moveRight (z : Input Symbol) : Input Symbol :=
  if z.atLeft then { z with atLeft := false } else
    match z.right with
    | [] => z
    | a :: r => ⟨a :: z.left, r, false⟩

/-- Move the input head in the indicated direction. -/
def move (z : Input Symbol) : SignType → Input Symbol
  | .neg => z.moveLeft
  | .zero => z
  | .pos => z.moveRight

/-- The stacks reconstruct the input and locate the head at the native bounded position. -/
structure Represents (z : Input Symbol) (input : List Symbol)
    (pos : Fin (input.length + 2)) : Prop where
  /-- The two stacks hold exactly the original input. -/
  contents : z.left.reverse ++ z.right = input
  /-- No symbols precede the left boundary. -/
  left_nil : z.atLeft = true → z.left = []
  /-- Native positions count the left boundary as zero. -/
  pos_eq : pos.val = if z.atLeft then 0 else z.left.length + 1

/-- Initialization agrees with the native initial head position, including on empty input. -/
theorem represents_init (input : List Symbol) :
    (init input).Represents input ⟨1, by omega⟩ := by
  constructor <;> simp [init]

namespace Represents

variable {z : Input Symbol} {input : List Symbol} {pos : Fin (input.length + 2)}

/-- The stacks retain exactly the number of input symbols. -/
theorem length_eq (h : z.Represents input pos) :
    z.left.length + z.right.length = input.length := by
  simpa only [List.length_append, List.length_reverse] using congrArg List.length h.contents

/-- A zipper read agrees with indexing the original input at the native head position. -/
theorem read_eq_getElem? (h : z.Represents input pos) :
    z.read = if pos.val = 0 then none else input[pos.val - 1]? := by
  rcases z with ⟨l, r, b⟩
  cases b with
  | false =>
    have hp : pos.val = l.length + 1 := h.pos_eq
    have hi : input = l.reverse ++ r := h.contents.symm
    simp [read, hp, hi, List.getElem?_append_right, List.head?_eq_getElem?]
  | true => simp [read, h.pos_eq]

/-- A zipper read agrees with the input symbol of any represented native configuration. -/
theorem read_eq_inputSymbol {k : ℕ} {State : Type*} {cfg : Cfg k Symbol State input}
    (h : z.Represents input cfg.inputPos) : z.read = cfg.inputSymbol := by
  rw [h.read_eq_getElem?]
  unfold Cfg.inputSymbol
  have := cfg.inputPos.isLt
  split_ifs <;> grind

/-- Moving left preserves the representation, with clamping at the left boundary. -/
theorem moveLeft (h : z.Represents input pos) :
    z.moveLeft.Represents input (moveInputPos pos .neg) := by
  have hm := val_moveInputPos_eq pos .neg
  simp only [SignType.cast] at hm
  rcases z with ⟨l, r, b⟩
  cases b with
  | true =>
    refine ⟨h.contents, h.left_nil, ?_⟩
    have hp : pos.val = 0 := h.pos_eq
    change (moveInputPos pos .neg).val = 0
    omega
  | false =>
    cases l with
    | nil =>
      refine ⟨h.contents, ?_, ?_⟩
      · simp [Input.moveLeft]
      · have hp : pos.val = 1 := h.pos_eq
        change (moveInputPos pos .neg).val = 0
        omega
    | cons a l =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [Input.moveLeft, List.reverse_cons, List.append_assoc] using h.contents
      · simp [Input.moveLeft]
      · have hp : pos.val = (a :: l).length + 1 := h.pos_eq
        simp only [List.length_cons] at hp
        change (moveInputPos pos .neg).val = l.length + 1
        omega

/-- Moving right preserves the representation, with clamping at the right boundary. -/
theorem moveRight (h : z.Represents input pos) :
    z.moveRight.Represents input (moveInputPos pos .pos) := by
  have hm := val_moveInputPos_eq pos .pos
  simp only [SignType.cast] at hm
  have hlen := h.length_eq
  rcases z with ⟨l, r, b⟩
  change l.length + r.length = input.length at hlen
  cases b with
  | true =>
    have hl : l = [] := h.left_nil rfl
    subst l
    refine ⟨h.contents, ?_, ?_⟩
    · simp [Input.moveRight]
    · have hp : pos.val = 0 := h.pos_eq
      change (moveInputPos pos .pos).val = 1
      omega
  | false =>
    cases r with
    | nil =>
      refine ⟨h.contents, h.left_nil, ?_⟩
      have hp : pos.val = l.length + 1 := h.pos_eq
      simp only [List.length_nil, Nat.add_zero] at hlen
      change (moveInputPos pos .pos).val = l.length + 1
      omega
    | cons a r =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [Input.moveRight, List.reverse_cons, List.append_assoc] using h.contents
      · simp [Input.moveRight]
      · have hp : pos.val = l.length + 1 := h.pos_eq
        simp only [List.length_cons] at hlen
        change (moveInputPos pos .pos).val = l.length + 1 + 1
        omega

/-- Each zipper move simulates the corresponding native bounded head move. -/
theorem move (h : z.Represents input pos) (d : SignType) :
    (z.move d).Represents input (moveInputPos pos d) := by
  cases d with
  | neg => exact h.moveLeft
  | zero =>
    change z.Represents input (moveInputPos pos 0)
    rwa [moveInputPos_zero]
  | pos => exact h.moveRight

end Represents
end Input
end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine, Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Bolton Bailey, Samuel Schlesinger
-/



/-!
# Raw two-stack work tapes

A work tape is stored as its current cell and two lists, nearest cell first. Blanks are retained:
moving beyond the stored interval extends it by one blank cell. Thus storage records the interval
visited by the head, independently of the number of times the machine revisits cells.
The relative read and representation proofs adapt the `BiTape` API of Bolton Bailey and
Samuel Schlesinger to raw lists.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.RawTape`: the current cell and the raw left and right stacks.
* `Turing.MultiTapeTM.ToTM2.RawTape.step`: native optional writing followed by head movement.
* `Turing.MultiTapeTM.ToTM2.RawTape.Represents`: correspondence with an integer-indexed native tape.

## Main results

* `Turing.MultiTapeTM.ToTM2.RawTape.Represents.step`: preservation of native tape semantics.
-/


namespace Turing.MultiTapeTM.ToTM2

/-- A work tape with raw stacks, ordered from the head outwards. Trailing blanks are retained. -/
@[ext] structure RawTape (Symbol : Type*) where
  /-- The cell under the head. -/
  head : Option Symbol
  /-- Cells strictly to the left, nearest first. -/
  left : List (Option Symbol)
  /-- Cells strictly to the right, nearest first. -/
  right : List (Option Symbol)
  deriving DecidableEq

namespace RawTape

variable {Symbol : Type*}

/-- A blank tape, initially storing just the cell at its head. -/
def init : RawTape Symbol := ⟨none, [], []⟩

instance : Inhabited (RawTape Symbol) := ⟨init⟩

/-- Perform an optional native write: `none` preserves the cell and `some none` erases it. -/
def write (t : RawTape Symbol) (w : Option (Option Symbol)) : RawTape Symbol :=
  { t with head := w.getD t.head }

@[simp] theorem write_none (t : RawTape Symbol) : t.write none = t := rfl

@[simp] theorem head_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).head = w.getD t.head := rfl

/-- Move left, extending the stored interval by a blank when the left stack is empty. -/
def moveLeft (t : RawTape Symbol) : RawTape Symbol :=
  ⟨t.left.headD none, t.left.tail, t.head :: t.right⟩

/-- Move right, extending the stored interval by a blank when the right stack is empty. -/
def moveRight (t : RawTape Symbol) : RawTape Symbol :=
  ⟨t.right.headD none, t.head :: t.left, t.right.tail⟩

/-- Apply a native work-tape action, writing before moving. -/
def step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) : RawTape Symbol :=
  match a.2 with
  | .neg => (t.write a.1).moveLeft
  | .zero => t.write a.1
  | .pos => (t.write a.1).moveRight

/-- Read at an integer offset relative to the head; unstored cells are blank. -/
def read (t : RawTape Symbol) : ℤ → Option Symbol
  | .ofNat 0 => t.head
  | .ofNat (n + 1) => t.right.getD n none
  | .negSucc n => t.left.getD n none

/-- The raw tape agrees with a native tape whose head is at `pos`. -/
def Represents (t : RawTape Symbol) (native : ℤ → Option Symbol) (pos : ℤ) : Prop :=
  ∀ z, t.read z = native (pos + z)

@[simp] theorem read_zero (t : RawTape Symbol) : t.read 0 = t.head := by simp [read]

@[simp] theorem read_init (z : ℤ) : (init : RawTape Symbol).read z = none := by
  cases z with
  | ofNat n => cases n <;> simp [read, init]
  | negSucc n => simp [read, init]

theorem read_write (t : RawTape Symbol) (w : Option (Option Symbol)) (z : ℤ) :
    (t.write w).read z = if z = 0 then w.getD t.head else t.read z := by
  cases z with
  | ofNat n => cases n <;> simp [read, write, add_eq_zero_iff_eq_neg]
  | negSucc n => simp [read, write]

theorem read_moveLeft (t : RawTape Symbol) (z : ℤ) :
    t.moveLeft.read z = t.read (z - 1) := by
  rcases t with ⟨h, l, r⟩
  cases z with
  | ofNat n =>
    cases n with
    | zero => cases l <;> rfl
    | succ n =>
      have he : (Int.ofNat (n + 1) : ℤ) - 1 = Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [he]
      cases n <;> rfl
  | negSucc n =>
    have he : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    rw [he]
    cases l <;> rfl

theorem read_moveRight (t : RawTape Symbol) (z : ℤ) :
    t.moveRight.read z = t.read (z + 1) := by
  rcases t with ⟨h, l, r⟩
  cases z with
  | ofNat n =>
    have he : (Int.ofNat n : ℤ) + 1 = Int.ofNat (n + 1) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [he]
    cases n <;> cases r <;> rfl
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n =>
      have he : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [he]
      rfl

theorem Represents.head {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.head = native pos := by
  simpa using h 0

theorem Represents.init : (init : RawTape Symbol).Represents (fun _ => none) 0 := by
  intro z
  exact read_init z

theorem Represents.write {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) (w : Option (Option Symbol)) :
    (t.write w).Represents (match w with
      | none => native
      | some s => Function.update native pos s) pos := by
  intro z
  rw [read_write]
  cases w with
  | none =>
    by_cases hz : z = 0
    · subst z; simpa using h 0
    · simpa [hz] using h z
  | some s =>
    by_cases hz : z = 0
    · subst z; simp
    · simpa [hz, show pos + z ≠ pos by omega] using h z

theorem Represents.moveLeft {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.moveLeft.Represents native (pos - 1) := by
  intro z
  rw [read_moveLeft, h]
  congr 1
  omega

theorem Represents.moveRight {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.moveRight.Represents native (pos + 1) := by
  intro z
  rw [read_moveRight, h]
  congr 1
  omega

/-- Raw execution preserves a native optional-write-and-move action, including erasing cells. -/
theorem Represents.step {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) (a : Option (Option Symbol) × SignType) :
    (t.step a).Represents (match a.1 with
      | none => native
      | some s => Function.update native pos s) (pos + a.2) := by
  rcases a with ⟨w, d⟩
  cases w <;> cases d
  · simpa only [RawTape.step, SignType.cast, add_zero] using h.write none
  · simpa only [RawTape.step, SignType.cast, sub_eq_add_neg] using (h.write none).moveLeft
  · simpa only [RawTape.step, SignType.cast] using (h.write none).moveRight
  · simpa only [RawTape.step, SignType.cast, add_zero] using h.write (some _)
  · simpa only [RawTape.step, SignType.cast, sub_eq_add_neg] using (h.write (some _)).moveLeft
  · simpa only [RawTape.step, SignType.cast] using (h.write (some _)).moveRight

@[simp] theorem left_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).left = t.left := rfl

@[simp] theorem right_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).right = t.right := rfl

@[simp] theorem length_left_moveLeft (t : RawTape Symbol) :
    t.moveLeft.left.length = t.left.length - 1 := by simp [moveLeft]

@[simp] theorem length_right_moveLeft (t : RawTape Symbol) :
    t.moveLeft.right.length = t.right.length + 1 := rfl

@[simp] theorem length_left_moveRight (t : RawTape Symbol) :
    t.moveRight.left.length = t.left.length + 1 := rfl

@[simp] theorem length_right_moveRight (t : RawTape Symbol) :
    t.moveRight.right.length = t.right.length - 1 := by simp [moveRight]

/-- The exact left-stack length after an action. -/
theorem length_left_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).left.length = match a.2 with
      | .neg => t.left.length - 1
      | .zero => t.left.length
      | .pos => t.left.length + 1 := by
  rcases a with ⟨w, d⟩
  cases d <;> simp only [step, length_left_moveLeft, length_left_moveRight, left_write]

/-- The exact right-stack length after an action. -/
theorem length_right_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).right.length = match a.2 with
      | .neg => t.right.length + 1
      | .zero => t.right.length
      | .pos => t.right.length - 1 := by
  rcases a with ⟨w, d⟩
  cases d <;> simp only [step, length_right_moveLeft, length_right_moveRight, right_write]

/-- The number of stored cells, including the current cell and stored blanks. -/
def span (t : RawTape Symbol) : ℕ := t.left.length + t.right.length + 1

@[simp] theorem span_init : (init : RawTape Symbol).span = 1 := rfl

@[simp] theorem span_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).span = t.span := rfl

/-- Storage grows only when the head moves beyond the previously stored interval. -/
theorem span_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).span = t.span +
      if (a.2 = .neg ∧ t.left = []) ∨ (a.2 = .pos ∧ t.right = []) then 1 else 0 := by
  rcases a with ⟨w, d⟩
  cases d <;> cases hl : t.left <;> cases hr : t.right <;>
    simp [span, length_left_step, length_right_step, hl, hr,
      Nat.add_comm, Nat.add_left_comm]

theorem span_step_le (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).span ≤ t.span + 1 := by
  rw [span_step]
  split_ifs <;> omega

end RawTape

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# A finite stack program for deterministic multi-tape machines

The input uses a pair of binary stacks and a flag for the left boundary. Each two-sided work
tape uses two stacks over `Option Bool`, with its current cell in finite control. Output is
accumulated in reverse order. A separate cleanup phase empties all auxiliary stacks before
reversing the output and resetting the control to Mathlib's canonical `haltList` convention.

## Main definitions

* `Turing.TM2.selectList`, `Turing.TM2.select`: finite case analysis in a TM2 statement.
* `Turing.MultiTapeTM.ToTM2.machine`: the finite-alphabet stack machine.
* `Turing.MultiTapeTM.ToTM2.program`: its running, cleanup and output-reversal phases.

## References

* [C. Papadimitriou, *Computational Complexity*, Chapter 2][Papadimitriou94]
-/


namespace Turing.TM2

open Stmt

variable {K : Type} {Γ : K → Type} {Λ State : Type}

/-- Finite case analysis compiles an arbitrary table on finite control to a fixed statement. -/
def selectList [DecidableEq State] (values : List State)
    (table : State → Stmt Γ Λ State) : Stmt Γ Λ State :=
  values.foldr (fun value rest => TM2.Stmt.branch (fun state => decide (state = value)) (table value) rest)
    halt

theorem stepAux_selectList [DecidableEq State] [DecidableEq K]
    (values : List State) (table : State → Stmt Γ Λ State)
    (state : State) (store : ∀ s, List (Γ s)) (h : state ∈ values) :
    stepAux (selectList values table) state store = stepAux (table state) state store := by
  induction values with
  | nil => simp at h
  | cons value values ih =>
    simp only [selectList, List.foldr_cons, stepAux]
    by_cases heq : state = value
    · subst value
      simp
    · simp only [heq, decide_false, Bool.cond_false]
      exact ih (List.mem_of_ne_of_mem heq h)

open scoped Classical in
/-- A table on a finite type uses only finitely many branches. -/
noncomputable def select [Fintype State] (table : State → Stmt Γ Λ State) : Stmt Γ Λ State :=
  selectList (Finset.univ.toList) table

theorem stepAux_select [Fintype State] [DecidableEq K]
    (table : State → Stmt Γ Λ State)
    (state : State) (store : ∀ s, List (Γ s)) :
    stepAux (select table) state store = stepAux (table state) state store := by
  classical
  exact stepAux_selectList _ _ _ _ (by simp)

end Turing.TM2

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- The four binary stacks and the two stacks for every work tape. -/
inductive Stack (k : ℕ) where
  | input | before | output | reversed
  | work (tape : Fin k) (right : Bool)
  deriving DecidableEq, Fintype

/-- Work stacks store blank cells explicitly; the input and output alphabets are binary. -/
abbrev Alphabet : Stack k → Type
  | .work _ _ => Option Bool
  | _ => Bool

instance (s : Stack k) : Fintype (Alphabet s) := by
  cases s <;> unfold Alphabet <;> infer_instance

/-- The three phases have no unbounded counters in their control. -/
inductive Label where
  | run | clean | reverse
  deriving DecidableEq

instance : Fintype Label := ⟨{.run, .clean, .reverse}, by intro l; cases l <;> simp⟩

/-- All unbounded data live on stacks. `symbol` and `busy` are scratch registers. -/
@[ext] structure Control (k : ℕ) (State : Type) where
  /-- The source state, or `none` when its final action has executed. -/
  state : Option State
  /-- Whether the bounded input head is at the blank before the word. -/
  atLeft : Bool
  /-- The current cell on each work tape. -/
  head : Fin k → Option Bool
  /-- A scratch register for input movement and output reversal. -/
  symbol : Option Bool
  /-- Whether the current cleanup round found a nonempty auxiliary stack. -/
  busy : Bool
  deriving Fintype

/-- Initial finite control, also restored before halting. -/
def initialControl (q : State) : Control k State :=
  ⟨some q, false, fun _ => none, none, false⟩

/-- A statement over the compiler's stack alphabets, phases and finite control. -/
abbrev Statement (k : ℕ) (State : Type) :=
  TM2.Stmt (Alphabet (k := k)) Label (Control k State)

open TM2.Stmt

/-- Write the current work cell, retaining the old value when no write is requested. -/
def writeWork (i : Fin k) (write : Option (Option Bool)) (next : Statement k State) :
    Statement k State :=
  load (fun v => { v with head := Function.update v.head i (write.getD (v.head i)) }) next

/-- Moving a work head transfers its old current cell to the opposite stack. -/
def moveWork (i : Fin k) (direction : SignType) (next : Statement k State) :
    Statement k State :=
  match direction with
  | .zero => next
  | .neg => push (.work i true) (fun v => v.head i)
      (pop (.work i false) (fun v a => { v with head := Function.update v.head i (a.getD none) })
        next)
  | .pos => push (.work i false) (fun v => v.head i)
      (pop (.work i true) (fun v a => { v with head := Function.update v.head i (a.getD none) })
        next)

/-- A fixed native work-tape action is a bounded straight-line stack statement. -/
def workAction (i : Fin k) (action : Option (Option Bool) × SignType)
    (next : Statement k State) : Statement k State :=
  writeWork i action.1 (moveWork i action.2 next)

/-- Move the bounded read-only input head. Empty stacks detect the two boundaries. -/
def moveInput (direction : SignType) (next : Statement k State) : Statement k State :=
  match direction with
  | .zero => next
  | .neg => TM2.Stmt.branch (fun v => v.atLeft) next
      (pop .before (fun v a => { v with symbol := a })
        (TM2.Stmt.branch (fun v => v.symbol.isSome)
          (push .input (fun v => v.symbol.getD false) next)
          (load (fun v => { v with atLeft := true }) next)))
  | .pos => TM2.Stmt.branch (fun v => v.atLeft) (load (fun v => { v with atLeft := false }) next)
      (pop .input (fun v a => { v with symbol := a })
        (TM2.Stmt.branch (fun v => v.symbol.isSome)
          (push .before (fun v => v.symbol.getD false) next) next))

/-- A source step updates every work tape, the input head, output and control. -/
def action (a : Turing.Action k Bool State) : Statement k State :=
  (List.finRange k).foldr (fun i next => workAction i (a.workTapes i) next)
    (moveInput a.inputTape
      (a.output.elim id (fun b => push .reversed (fun _ => b))
        (load (fun v => { v with state := a.state, symbol := none, busy := false })
          (goto (fun _ => .run)))))

/-- Stacks discarded before output reversal. -/
def auxiliaries (k : ℕ) : List (Stack k) :=
  [.input, .before] ++ (List.finRange k).flatMap (fun i => [.work i false, .work i true])

/-- Discard one cell from each auxiliary stack and remember whether any was nonempty. -/
def discard (s : Stack k) (next : Statement k State) : Statement k State :=
  pop s (fun v a => { v with busy := v.busy || a.isSome }) next

/-- A cleanup round either reduces auxiliary storage or advances to output reversal. -/
def clean : Statement k State :=
  load (fun v => { v with busy := false })
    ((auxiliaries k).foldr discard
      (TM2.Stmt.branch (fun v => v.busy) (goto (fun _ => .clean)) (goto (fun _ => .reverse))))

/-- The fixed program has finite control and a finite alphabet on every stack. -/
def program [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State) :
    Label → Statement k State
  | .run => peek .input (fun v a => { v with symbol := a })
      (TM2.select fun v => match v.state with
        | none => goto (fun _ => .clean)
        | some q => action (transition q (if v.atLeft then none else v.symbol) v.head))
  | .clean => clean
  | .reverse => pop .reversed (fun v a => { v with symbol := a })
      (TM2.Stmt.branch (fun v => v.symbol.isSome)
        (push .output (fun v => v.symbol.getD false) (goto (fun _ => .reverse)))
        (load (fun _ => initialControl q₀) halt))

/-- The actual Mathlib `FinTM2` produced by the reverse compiler. -/
abbrev machine [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State) :
    FinTM2 where
  K := Stack k
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .run
  σ := Control k State
  initialState := initialControl q₀
  m := program q₀ transition

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Raw configurations for the multi-tape to TM2 compiler

## Main definitions

* `Turing.MultiTapeTM.ToTM2.Data`: finite stacks representing a binary native configuration.
* `Turing.MultiTapeTM.ToTM2.Data.step`: apply one native action to the raw configuration.
* `Turing.MultiTapeTM.ToTM2.Data.run`: execute a native machine with raw stacks.
* `Turing.MultiTapeTM.ToTM2.Data.Represents`: agreement with a native configuration.

## Main results

* `Turing.MultiTapeTM.ToTM2.Data.represents_run`: raw execution agrees with native execution.
* `Turing.MultiTapeTM.ToTM2.Data.input_length_run`: input storage is exactly the input length.
* `Turing.MultiTapeTM.ToTM2.Data.output_prefix_run`: chronological output grows by extension.
-/


namespace Turing.MultiTapeTM.ToTM2

/-- A native binary configuration stored as finite stacks, with chronological output. -/
@[ext]
structure Data (k : ℕ) (State : Type) where
  /-- The current state, or `none` after halting. -/
  state : Option State
  /-- The bounded read-only input zipper. -/
  input : Input Bool
  /-- The work tapes, retaining all visited cells. -/
  work : Fin k → RawTape Bool
  /-- Symbols emitted so far, in chronological order. -/
  output : List Bool

namespace Data

variable {k : ℕ} {State : Type}

/-- Initialize the input zipper and blank work tapes. -/
def init (q₀ : State) (input : List Bool) : Data k State :=
  ⟨some q₀, Input.init input, fun _ => RawTape.init, []⟩

/-- Apply an action, including the output and movement of its final halting step. -/
def step (d : Data k State) (a : Action k Bool State) : Data k State where
  state := a.state
  input := d.input.move a.inputTape
  work i := (d.work i).step (a.workTapes i)
  output := d.output ++ a.output.toList

/-- Select and apply the native transition, staying put once halted. -/
noncomputable def totalStep (tm : MultiTapeTM k Bool State) (d : Data k State) : Data k State :=
  match d.state with
  | none => d
  | some q => d.step (tm.tr q d.input.read (fun i => (d.work i).head))

/-- Execute a fixed number of total steps from an arbitrary raw configuration. -/
noncomputable def runFrom (tm : MultiTapeTM k Bool State) (d : Data k State) (t : ℕ) :
    Data k State :=
  (totalStep tm)^[t] d

/-- Execute a fixed number of total steps from the initial raw configuration. -/
noncomputable def run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    Data k State :=
  runFrom tm (init tm.q₀ input) t

/-- Raw fields agree with the corresponding native state, heads, tapes and output. -/
structure Represents (d : Data k State) {sourceInput : List Bool}
    (cfg : Cfg k Bool State sourceInput) : Prop where
  /-- The control states agree. -/
  state : d.state = cfg.state
  /-- The input zipper represents the native bounded head. -/
  input : d.input.Represents sourceInput cfg.inputPos
  /-- Each work tape represents its native integer-indexed tape and head. -/
  work : ∀ i, (d.work i).Represents (cfg.workTapes i) (cfg.workTapePos i)
  /-- Output is chronological in both representations. -/
  output : d.output = cfg.output

@[simp]
theorem runFrom_zero (tm : MultiTapeTM k Bool State) (d : Data k State) :
    runFrom tm d 0 = d := by rfl

/-- The next raw configuration is one total step from the preceding configuration. -/
theorem runFrom_succ (tm : MultiTapeTM k Bool State) (d : Data k State) (t : ℕ) :
    runFrom tm d (t + 1) = totalStep tm (runFrom tm d t) := by
  exact Function.iterate_succ_apply' _ _ _

@[simp]
theorem run_zero (tm : MultiTapeTM k Bool State) (input : List Bool) :
    run tm input 0 = init tm.q₀ input := by rfl

/-- The next raw configuration on an input is obtained by one total step. -/
theorem run_succ (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    run tm input (t + 1) = totalStep tm (run tm input t) := by
  exact runFrom_succ _ _ _

/-- Halted raw configurations are fixed by the total step. -/
theorem totalStep_of_halt (tm : MultiTapeTM k Bool State) {d : Data k State}
    (h : d.state = none) : totalStep tm d = d := by
  rw [totalStep, h]

/-- A live raw configuration applies the transition selected from its current reads. -/
theorem totalStep_of_state (tm : MultiTapeTM k Bool State) {d : Data k State} {q : State}
    (h : d.state = some q) :
    totalStep tm d = d.step (tm.tr q d.input.read (fun i => (d.work i).head)) := by
  rw [totalStep, h]

namespace Represents

variable {d : Data k State} {sourceInput : List Bool} {cfg : Cfg k Bool State sourceInput}

/-- Initialization represents the native initial configuration. -/
theorem init (q₀ : State) (input : List Bool) :
    (Data.init (k := k) q₀ input).Represents (Cfg.init q₀ input) :=
  ⟨rfl, Input.represents_init input, fun _ => RawTape.Represents.init, rfl⟩

/-- Applying the same action preserves every field of the representation. -/
theorem step (h : d.Represents cfg) (a : Action k Bool State) :
    (d.step a).Represents (a.apply cfg) :=
  ⟨rfl, h.input.move a.inputTape, fun i => (h.work i).step (a.workTapes i),
    congrArg (· ++ a.output.toList) h.output⟩

/-- Raw and native configurations select the same action and take corresponding total steps. -/
theorem totalStep (h : d.Represents cfg) (tm : MultiTapeTM k Bool State) :
    (Data.totalStep tm d).Represents (tm.step cfg) := by
  cases hs : d.state with
  | none =>
    rw [Data.totalStep_of_halt tm hs, tm.step_of_halt (h.state.symm.trans hs)]
    exact h
  | some q =>
    rw [Data.totalStep_of_state tm hs, tm.step_of_state (h.state.symm.trans hs)]
    have hi : d.input.read = cfg.inputSymbol := h.input.read_eq_inputSymbol
    have hw : (fun i => (d.work i).head) = cfg.workTapeSymbols :=
      funext fun i => (h.work i).head
    rw [hi, hw]
    exact h.step _

/-- Any number of raw total steps represents the same number of native total steps. -/
theorem runFrom (h : d.Represents cfg) (tm : MultiTapeTM k Bool State) (t : ℕ) :
    (Data.runFrom tm d t).Represents (tm.runFrom cfg t) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [Data.runFrom_succ, MultiTapeTM.runFrom, Function.iterate_succ_apply',
      ← MultiTapeTM.runFrom]
    exact ih.totalStep tm

end Represents

/-- Raw execution from initialization agrees with the native execution, even after halting. -/
theorem represents_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).Represents (tm.runFrom (tm.initCfg input) t) :=
  (Represents.init tm.q₀ input).runFrom tm t

/-- At every time, the raw input stacks retain exactly the original input length. -/
theorem input_length_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).input.left.length + (run tm input t).input.right.length = input.length :=
  (represents_run tm input t).input.length_eq

/-- The raw output is exactly the native chronological output. -/
theorem output_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).output = (tm.runFrom (tm.initCfg input) t).output :=
  (represents_run tm input t).output

/-- The raw control state agrees with the native state at every time. -/
theorem state_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).state = (tm.runFrom (tm.initCfg input) t).state :=
  (represents_run tm input t).state

/-- Each action only appends to the output. -/
theorem output_prefix_step (d : Data k State) (a : Action k Bool State) :
    d.output <+: (d.step a).output :=
  ⟨a.output.toList, rfl⟩

/-- Total steps only append to the output, including a step which halts. -/
theorem output_prefix_totalStep (tm : MultiTapeTM k Bool State) (d : Data k State) :
    d.output <+: (totalStep tm d).output := by
  cases hs : d.state with
  | none => rw [totalStep_of_halt tm hs]
  | some q => rw [totalStep_of_state tm hs]; exact output_prefix_step _ _

/-- Earlier raw outputs are prefixes of all later raw outputs. -/
theorem output_prefix_run (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t u : ℕ} (h : t ≤ u) : (run tm input t).output <+: (run tm input u).output := by
  induction u, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ u _ ih =>
    rw [run_succ]
    exact ih.trans (output_prefix_totalStep tm _)

/-- The amount of output never decreases. -/
theorem output_length_run_mono (tm : MultiTapeTM k Bool State) (input : List Bool) :
    Monotone (fun t => (run tm input t).output.length) :=
  fun _ _ h => (output_prefix_run tm input h).length_le

/-- Raw execution stays at its final configuration after halting. -/
theorem run_eq_of_halt (tm : MultiTapeTM k Bool State) (input : List Bool) {t u : ℕ}
    (hle : t ≤ u) (hhalt : (run tm input t).state = none) :
    run tm input u = run tm input t := by
  induction u, hle using Nat.le_induction with
  | base => rfl
  | succ u _ ih => rw [run_succ, ih, totalStep_of_halt tm hhalt]

/-- Every intermediate output is bounded by the output of a terminating run. -/
theorem output_length_run_le_of_halt (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t : ℕ} (hhalt : (run tm input t).state = none) (u : ℕ) :
    (run tm input u).output.length ≤ (run tm input t).output.length := by
  rcases le_total u t with h | h
  · exact output_length_run_mono tm input h
  · rw [run_eq_of_halt tm input h hhalt]

/-- Every raw output is a prefix of the complete output of a terminating native computation. -/
theorem output_prefix_run_of_computes {tm : MultiTapeTM k Bool State}
    {input output : List Bool} (h : tm.Computes input output) (t : ℕ) :
    (run tm input t).output <+: output := by
  obtain ⟨u, hhalt, hout⟩ := h
  have hraw : (run tm input u).output = output := (output_run tm input u).trans hout
  rcases le_total t u with h | h
  · exact hraw ▸ output_prefix_run tm input h
  · rw [run_eq_of_halt tm input h ((state_run tm input u).trans hhalt), hraw]

/-- A terminating native output bounds every intermediate raw output, without a time term. -/
theorem output_length_run_le_of_computes {tm : MultiTapeTM k Bool State}
    {input output : List Bool} (h : tm.Computes input output) (t : ℕ) :
    (run tm input t).output.length ≤ output.length :=
  (output_prefix_run_of_computes h t).length_le

end Data
end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Stack representation for the reverse TM2 compiler

Each native transition compiles to one fixed Mathlib stack-machine statement. The finite control
holds the current work cells; raw stacks retain blank cells and preserve the two-sided geometry.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.encode`: represent a raw configuration at a source-step boundary.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Finite control corresponding to raw simulation data, with arbitrary scratch registers. -/
def control (d : Data k State) (symbol : Option Bool := none) (busy : Bool := false) :
    Control k State := ⟨d.state, d.input.atLeft, fun i => (d.work i).head, symbol, busy⟩

/-- The stack representation keeps output in reverse order until cleanup. -/
def store (d : Data k State) : (s : Stack k) → List (Alphabet s)
  | .input => d.input.right
  | .before => d.input.left
  | .output => []
  | .reversed => d.output.reverse
  | .work i false => (d.work i).left
  | .work i true => (d.work i).right

/-- The TM2 configuration at a source-step boundary. -/
def encode (d : Data k State) : TM2.Cfg (Alphabet (k := k)) Label (Control k State) :=
  ⟨some .run, control d, store d⟩

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Compiled input movement and output emission

## Main definitions

* `Turing.MultiTapeTM.ToTM2.inputSymbol`: the scratch symbol after compiled input movement.

## Main results

* `Turing.MultiTapeTM.ToTM2.stepAux_moveInput`: compiled movement agrees with the raw input
  zipper, without a validity assumption.
* `Turing.MultiTapeTM.ToTM2.stepAux_finish`: emit an optional bit and restore boundary control.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Input movement retains scratch at the left boundary and otherwise remembers the popped bit. -/
def inputSymbol (d : Data k State) (direction : SignType) (scratch : Option Bool) : Option Bool :=
  if d.input.atLeft then scratch else
    match direction with
    | .zero => scratch
    | .neg => d.input.left.head?
    | .pos => d.input.right.head?

/-- The compiled input movement agrees with the zipper on every raw configuration. -/
theorem stepAux_moveInput (d : Data k State) (direction : SignType)
    (next : Statement k State) (scratch : Option Bool) (busy : Bool) :
    TM2.stepAux (moveInput direction next) (control d scratch busy) (store d) =
      TM2.stepAux next
        (control { d with input := d.input.move direction } (inputSymbol d direction scratch) busy)
        (store { d with input := d.input.move direction }) := by
  classical
  rcases d with ⟨state, ⟨left, right, atLeft⟩, work, output⟩
  cases direction <;> cases atLeft
  all_goals try rfl
  all_goals cases left <;> cases right
  all_goals
    simp only [moveInput, TM2.stepAux, control, store, inputSymbol, Input.move, Input.moveLeft,
      Input.moveRight]
  all_goals simp only [Alphabet, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
    Option.isSome_none, Option.isSome_some, Bool.cond_true, Bool.cond_false,
    Option.getD_some, Bool.false_eq_true, ↓reduceIte]
  all_goals
    congr 1
    funext s
    cases s with
    | work i side => cases side <;> simp [Function.update, store]
    | output => simp only [Function.update, store]; rfl
    | _ => simp [Function.update, store]

/-- Emitting an optional bit and loading the next source state restores a step boundary. -/
theorem stepAux_finish (d : Data k State) (state : Option State) (output : Option Bool)
    (scratch : Option Bool) (busy : Bool) :
    TM2.stepAux
      (output.elim id (fun b => TM2.Stmt.push .reversed (fun _ => b))
        (TM2.Stmt.load (fun v => { v with state := state, symbol := none, busy := false })
          (TM2.Stmt.goto (fun _ => .run))))
      (control d scratch busy) (store d) =
      encode { d with state := state, output := d.output ++ output.toList } := by
  classical
  cases output with
  | none =>
    simp only [Option.elim, encode, Option.toList_none, List.append_nil]
    congr 1
  | some b =>
    simp only [Option.elim, TM2.stepAux, encode, Option.toList_some]
    congr 1
    funext s
    cases s with
    | work i side => cases side <;> simp [Function.update, store]
    | output => simp only [Function.update, store]; rfl
    | _ => simp [Function.update, store]

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Execution correspondence for the reverse TM2 compiler

Each native transition compiles to one fixed Mathlib stack-machine statement. The finite control
holds the current work cells; raw stacks retain blank cells and preserve the two-sided geometry.

## Main results

* `Turing.MultiTapeTM.ToTM2.stepAux_action`: a compiled action realizes the raw tape update.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

private theorem control_write (d : Data k State) (i : Fin k) (w : Option (Option Bool))
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with
      head := (Function.update (control d symbol busy).head i
        (w.getD ((control d symbol busy).head i))) }
      = control { d with work := Function.update d.work i ((d.work i).write w) } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i <;> simp [Function.update, control, RawTape.write, h]

private theorem store_write (d : Data k State) (i : Fin k) (w : Option (Option Bool)) :
    store { d with work := Function.update d.work i ((d.work i).write w) } = store d := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i <;> cases side <;> simp [store, RawTape.write, h]
  | _ => rfl

private theorem stepAux_writeWork (d : Data k State) (i : Fin k) (w : Option (Option Bool))
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (writeWork i w next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).write w) } symbol busy)
        (store { d with work := Function.update d.work i ((d.work i).write w) }) := by
  simp only [writeWork, TM2.stepAux, control_write, store_write]

private theorem control_moveLeft (d : Data k State) (i : Fin k)
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with head := (Function.update (control d symbol busy).head i
      (((store d (.work i false)).head?).getD none)) } =
      control { d with work := Function.update d.work i (d.work i).moveLeft } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i
  · subst j
    simp only [control, store, RawTape.moveLeft, List.headD_eq_head?_getD, Function.update_self]
  · simp only [control, store, RawTape.moveLeft, List.headD_eq_head?_getD, Function.update_of_ne h]

private theorem store_moveLeft (d : Data k State) (i : Fin k) :
    Function.update
      (Function.update (store d) (.work i true) ((d.work i).head :: (d.work i).right))
      (.work i false) (d.work i).left.tail =
      store { d with work := Function.update d.work i (d.work i).moveLeft } := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i
    · subst j; cases side <;> simp [Function.update, store, RawTape.moveLeft]
    · cases side <;> simp [Function.update, store, h]
  | _ => rfl

private theorem control_moveRight (d : Data k State) (i : Fin k)
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with head := (Function.update (control d symbol busy).head i
      (((store d (.work i true)).head?).getD none)) } =
      control { d with work := Function.update d.work i (d.work i).moveRight } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i
  · subst j
    simp only [control, store, RawTape.moveRight, List.headD_eq_head?_getD, Function.update_self]
  · simp only [control, store, RawTape.moveRight, List.headD_eq_head?_getD, Function.update_of_ne h]

private theorem store_moveRight (d : Data k State) (i : Fin k) :
    Function.update
      (Function.update (store d) (.work i false) ((d.work i).head :: (d.work i).left))
      (.work i true) (d.work i).right.tail =
      store { d with work := Function.update d.work i (d.work i).moveRight } := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i
    · subst j; cases side <;> simp [Function.update, store, RawTape.moveRight]
    · cases side <;> simp [Function.update, store, h]
  | _ => rfl

private theorem stepAux_moveWork (d : Data k State) (i : Fin k) (direction : SignType)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (moveWork i direction next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).step (none, direction)) }
          symbol busy)
        (store
          { d with work := Function.update d.work i ((d.work i).step (none, direction)) }) := by
  cases direction with
  | zero => simp [moveWork, RawTape.step, RawTape.write, Function.update_eq_self]
  | neg =>
    simp only [moveWork, TM2.stepAux]
    rw [Function.update_of_ne (by simp : Stack.work i false ≠ Stack.work i true)]
    change TM2.stepAux next
      { control d symbol busy with head := (Function.update (control d symbol busy).head i
        (((store d (.work i false)).head?).getD none)) }
      (Function.update
        (Function.update (store d) (.work i true) ((d.work i).head :: (d.work i).right))
        (.work i false) (d.work i).left.tail) = _
    rw [control_moveLeft, store_moveLeft]
    rfl
  | pos =>
    simp only [moveWork, TM2.stepAux]
    rw [Function.update_of_ne (by simp : Stack.work i true ≠ Stack.work i false)]
    change TM2.stepAux next
      { control d symbol busy with head := (Function.update (control d symbol busy).head i
        (((store d (.work i true)).head?).getD none)) }
      (Function.update
        (Function.update (store d) (.work i false) ((d.work i).head :: (d.work i).left))
        (.work i true) (d.work i).right.tail) = _
    rw [control_moveRight, store_moveRight]
    rfl

private theorem stepAux_workAction (d : Data k State) (i : Fin k)
    (a : Option (Option Bool) × SignType) (next : Statement k State)
    (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (workAction i a next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).step a) } symbol busy)
        (store { d with work := Function.update d.work i ((d.work i).step a) }) := by
  rw [workAction, stepAux_writeWork, stepAux_moveWork]
  cases a with | mk w direction =>
    cases direction <;> simp [RawTape.step, RawTape.write, Function.update_idem]

private def applyWorks (d : Data k State)
    (a : Fin k → Option (Option Bool) × SignType) (indices : List (Fin k)) : Data k State :=
  indices.foldl (fun d i => { d with work := Function.update d.work i ((d.work i).step (a i)) }) d

private theorem stepAux_workActions (indices : List (Fin k))
    (a : Fin k → Option (Option Bool) × SignType) (d : Data k State)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (indices.foldr (fun i next => workAction i (a i) next) next)
      (control d symbol busy) (store d) =
      TM2.stepAux next (control (applyWorks d a indices) symbol busy)
        (store (applyWorks d a indices)) := by
  induction indices generalizing d with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldr_cons, stepAux_workAction, ih]
    rfl

private theorem applyWorks_eq (indices : List (Fin k)) (h : indices.Nodup)
    (a : Fin k → Option (Option Bool) × SignType) (d : Data k State) :
    applyWorks d a indices =
      { d with work := fun i => if i ∈ indices then (d.work i).step (a i) else d.work i } := by
  induction indices generalizing d with
  | nil => simp [applyWorks]
  | cons i indices ih =>
    rw [List.nodup_cons] at h
    change applyWorks { d with work := Function.update d.work i ((d.work i).step (a i)) }
      a indices = _
    rw [ih h.2]
    apply Data.ext <;> try rfl
    funext j
    by_cases hj : j = i
    · subst j
      simp [h.1]
    · by_cases hmem : j ∈ indices <;> simp [hj, hmem]

/-- Each work tape is updated once, in a fixed straight-line statement. -/
private theorem stepAux_allWork (a : Fin k → Option (Option Bool) × SignType) (d : Data k State)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux ((List.finRange k).foldr (fun i next => workAction i (a i) next) next)
      (control d symbol busy) (store d) =
      TM2.stepAux next (control { d with work := fun i => (d.work i).step (a i) } symbol busy)
        (store { d with work := fun i => (d.work i).step (a i) }) := by
  rw [stepAux_workActions, applyWorks_eq _ (List.nodup_finRange k)]
  simp only [List.mem_finRange, ↓reduceIte]

/-- One complete compiled action realizes the native update on finite tape data. -/
theorem stepAux_action (d : Data k State) (a : Turing.Action k Bool State)
    (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (action a) (control d symbol busy) (store d) = encode (d.step a) := by
  rw [action, stepAux_allWork, stepAux_moveInput, stepAux_finish]
  rfl

/-- One live source transition is exactly one Mathlib stack-machine transition. -/
theorem step_encode [Fintype State] (tm : MultiTapeTM k Bool State) (d : Data k State)
    {q : State} (hq : d.state = some q) :
    TM2.step (program tm.q₀ tm.tr) (encode d) = some (encode (Data.totalStep tm d)) := by
  simp only [encode, TM2.step, program, TM2.stepAux]
  rw [TM2.stepAux_select]
  change some (TM2.stepAux
    (match d.state with
    | none => TM2.Stmt.goto (fun _ => .clean)
    | some q => action (tm.tr q (if d.input.atLeft then none else d.input.right.head?)
        (fun i => (d.work i).head)))
    (control d d.input.right.head? false) (store d)) = _
  rw [hq, stepAux_action, Data.totalStep_of_state tm hq]
  rfl

/-- A halted source starts cleanup on the following target step. -/
theorem step_encode_halt [Fintype State] (tm : MultiTapeTM k Bool State) (d : Data k State)
    (hq : d.state = none) :
    TM2.step (program tm.q₀ tm.tr) (encode d) =
      some ⟨some .clean, control d d.input.right.head? false, store d⟩ := by
  simp only [encode, TM2.step, program, TM2.stepAux]
  rw [TM2.stepAux_select]
  simp only [control, hq, TM2.stepAux, store]

/-- Native initialization already has the stack layout required by the compiler. -/
theorem encode_init [Fintype State] (tm : MultiTapeTM k Bool State) (input : List Bool) :
    encode (Data.init tm.q₀ input) = initList (machine tm.q₀ tm.tr) input := by
  apply congrArg (fun s =>
    (⟨some .run, initialControl tm.q₀, s⟩ : TM2.Cfg (Alphabet (k := k)) Label (Control k State)))
  funext s
  cases s with
  | work i b => cases b <;> rfl
  | _ => rfl

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Whole-run correspondence before cleanup

The compiler executes exactly one source transition per TM2 transition until the first halting
source configuration. Its next transition enters cleanup. These statements include the final
source action, which may write, move heads and emit a bit while halting.

## Main results

* `Turing.MultiTapeTM.ToTM2.iterate_encode`: correspondence of every source execution prefix.
* `Turing.MultiTapeTM.ToTM2.prefixEvals`: the same correspondence with Mathlib's partial clock.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type} [Fintype State]

private theorem stepTotal_encode (tm : MultiTapeTM k Bool State) (d : Data k State)
    {q : State} (hq : d.state = some q) :
    TM2.stepTotal (program tm.q₀ tm.tr) (encode d) = encode (Data.totalStep tm d) :=
  Option.some.inj (step_encode tm d hq)

theorem stepTotal_encode_halt (tm : MultiTapeTM k Bool State) (d : Data k State)
    (hq : d.state = none) :
    TM2.stepTotal (program tm.q₀ tm.tr) (encode d) =
      ⟨some .clean, control d d.input.right.head? false, store d⟩ :=
  Option.some.inj (step_encode_halt tm d hq)

/-- Every source prefix through the first halted configuration is reproduced exactly. -/
theorem iterate_encode (tm : MultiTapeTM k Bool State) (input : List Bool) {t : ℕ}
    (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    (TM2.stepTotal (program tm.q₀ tm.tr))^[i] (initList (machine tm.q₀ tm.tr) input) =
      encode (Data.run tm input i) := by
  induction i with
  | zero =>
    rw [Data.run_zero]
    exact (encode_init tm input).symm
  | succ i ih =>
    have hstep :
        (TM2.stepTotal (program tm.q₀ tm.tr))^[i + 1] (initList (machine tm.q₀ tm.tr) input) =
          TM2.stepTotal (program tm.q₀ tm.tr)
            ((TM2.stepTotal (program tm.q₀ tm.tr))^[i] (initList (machine tm.q₀ tm.tr) input)) :=
      Function.iterate_succ_apply' _ i _
    rw [hstep, ih (by omega)]
    have hn : (Data.run tm input i).state ≠ none := by
      rw [Data.state_run]
      exact ht.not_halted (by omega)
    cases hq : (Data.run tm input i).state with
    | none => exact False.elim (hn hq)
    | some q => rw [stepTotal_encode tm _ hq, Data.run_succ]

/-- The partial clock retains a successor throughout each source execution prefix. -/
private theorem partial_iterate_encode (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t : ℕ} (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    (fun c => c.bind (machine tm.q₀ tm.tr).step)^[i]
      (some (initList (machine tm.q₀ tm.tr) input)) = some (encode (Data.run tm input i)) := by
  induction i with
  | zero =>
    rw [Data.run_zero]
    exact congrArg some (encode_init tm input).symm
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hn : (Data.run tm input i).state ≠ none := by
      rw [Data.state_run]
      exact ht.not_halted (by omega)
    cases hq : (Data.run tm input i).state with
    | none => exact False.elim (hn hq)
    | some q =>
      change TM2.step (program tm.q₀ tm.tr) (encode (Data.run tm input i)) = _
      rw [step_encode tm _ hq, Data.run_succ]

/-- Mathlib's partial execution reaches each source prefix in exactly that many transitions. -/
def prefixEvals (tm : MultiTapeTM k Bool State) (input : List Bool) {t : ℕ}
    (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step
      (initList (machine tm.q₀ tm.tr) input) (some (encode (Data.run tm input i))) i :=
  ⟨⟨i, partial_iterate_encode tm input ht hi⟩, le_rfl⟩

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Canonical cleanup for the multi-tape to TM2 compiler

Cleanup discards the input and work stacks, reverses the accumulated output onto the output
stack, and resets finite control. Existing output is retained as a suffix.

## Main definitions

* `StateTransition.EvalsToInTime.cons`, `.mono`: prepend one transition or enlarge the
  clock of a bounded partial execution.
* `Turing.MultiTapeTM.ToTM2.auxiliaryLength`: storage discarded by cleanup.
* `Turing.MultiTapeTM.ToTM2.totalStackLength`: storage on all stacks, including input and output.

## Main results

* `Turing.MultiTapeTM.ToTM2.cleanupEvals`: canonical halting with an explicit linear clock.

## References

* [C. Papadimitriou, *Computational Complexity*, Chapter 2][Papadimitriou94]
-/


namespace StateTransition.EvalsToInTime

/-- Prepend one transition to a bounded execution. -/
def cons {α : Type} {f : α → Option α} {a b c : α} {n : ℕ}
    (hs : f a = some b) (h : EvalsToInTime f b (some c) n) :
    EvalsToInTime f a (some c) (n + 1) where
  steps := h.steps + 1
  evals_in_steps := by
    rw [Function.iterate_succ_apply]
    change (flip bind f)^[h.steps] (f a) = some c
    rw [hs]
    exact h.evals_in_steps
  steps_le_m := Nat.add_le_add_right h.steps_le_m 1

/-- Increase the clock of a bounded execution. -/
def mono {α : Type} {f : α → Option α} {a c : α} {m n : ℕ}
    (h : EvalsToInTime f a (some c) m) (hmn : m ≤ n) :
    EvalsToInTime f a (some c) n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hmn⟩

end StateTransition.EvalsToInTime

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Exactly the stacks other than the two output stacks are discarded. -/
@[simp] theorem mem_auxiliaries (s : Stack k) :
    s ∈ auxiliaries k ↔ s ≠ .output ∧ s ≠ .reversed := by
  cases s with
  | work i b => cases b <;> simp [auxiliaries]
  | _ => simp [auxiliaries]

/-- Each auxiliary is popped exactly once in a cleanup round. -/
theorem auxiliaries_nodup (k : ℕ) : (auxiliaries k).Nodup := by
  have hp : List.Pairwise (Function.onFun List.Disjoint
      (fun i : Fin k => [Stack.work i false, Stack.work i true])) (List.finRange k) := by
    apply (List.nodup_finRange k).imp
    intro i j hij
    simp [Function.onFun, List.disjoint_left, hij]
  simpa [auxiliaries, List.nodup_append, List.nodup_flatMap, List.disjoint_left] using hp

/-- Pop each named stack once; the list is assumed duplicate-free when used operationally. -/
private def poppedStore (ss : List (Stack k)) (store : ∀ s : Stack k, List (Alphabet s)) :
    ∀ s : Stack k, List (Alphabet s) :=
  fun s => if s ∈ ss then (store s).tail else store s

private theorem poppedStore_cons (s : Stack k) (ss : List (Stack k))
    (store : ∀ s : Stack k, List (Alphabet s)) (h : s ∉ ss) :
    poppedStore ss (Function.update store s (store s).tail) = poppedStore (s :: ss) store := by
  funext t
  by_cases ht : t = s
  · subst t
    simp [poppedStore, h]
  · simp [poppedStore, ht]

private theorem any_update (s : Stack k) (ss : List (Stack k))
    (store : ∀ s : Stack k, List (Alphabet s)) (h : s ∉ ss) :
    ss.any (fun t => ((Function.update store s (store s).tail) t).head?.isSome) =
      ss.any (fun t => (store t).head?.isSome) := by
  induction ss with
  | nil => rfl
  | cons t ss ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.any_cons, Function.update_of_ne (Ne.symm h.1), ih h.2]

/-- The straight-line discard statement records whether a stack was nonempty before popping. -/
private theorem stepAux_discard (ss : List (Stack k)) (hss : ss.Nodup)
    (next : Statement k State) (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux (ss.foldr discard next) v store =
      TM2.stepAux next
        { v with busy := v.busy || ss.any (fun s => (store s).head?.isSome) }
        (poppedStore ss store) := by
  induction ss generalizing v store with
  | nil =>
    have hs : poppedStore [] store = store := by funext s; simp [poppedStore]
    simp only [List.foldr_nil, List.any_nil, Bool.or_false, hs]
  | cons s ss ih =>
    rw [List.nodup_cons] at hss
    simp only [List.foldr_cons, discard, TM2.stepAux]
    rw [ih hss.2, poppedStore_cons s ss store hss.1, any_update s ss store hss.1]
    simp [Bool.or_assoc]

/-- Total auxiliary storage before a cleanup round. -/
def auxiliaryLength (store : ∀ s : Stack k, List (Alphabet s)) : ℕ :=
  ∑ s : Stack k, if s ∈ auxiliaries k then (store s).length else 0

/-- Total stack storage, counting both output stacks and all auxiliary stacks. -/
def totalStackLength (cfg : TM2.Cfg (Alphabet (k := k)) Label (Control k State)) : ℕ :=
  ∑ s : Stack k, (cfg.stk s).length

/-- Every stack contributes exactly once to the storage accounting. -/
theorem totalStackLength_eq (cfg : TM2.Cfg (Alphabet (k := k)) Label (Control k State)) :
    totalStackLength cfg = auxiliaryLength cfg.stk +
      (cfg.stk .reversed).length + (cfg.stk .output).length := by
  classical
  calc
    _ = ∑ s : Stack k, ((if s ∈ auxiliaries k then (cfg.stk s).length else 0) +
        (if s = .reversed then (cfg.stk s).length else 0) +
        (if s = .output then (cfg.stk s).length else 0)) := by
      apply Finset.sum_congr rfl
      intro s hs
      cases s <;> simp
    _ = _ := by simp [auxiliaryLength, Finset.sum_add_distrib]

/-- Whether a cleanup round encounters a nonempty auxiliary stack. -/
private def auxiliaryBusy (store : ∀ s : Stack k, List (Alphabet s)) : Bool :=
  (auxiliaries k).any (fun s => (store s).head?.isSome)

/-- A round pops all auxiliaries, preserving both output stacks. -/
private theorem stepAux_clean (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux clean v store =
      ⟨some (if auxiliaryBusy store then .clean else .reverse),
        { v with busy := auxiliaryBusy store }, poppedStore (auxiliaries k) store⟩ := by
  simp only [clean, TM2.stepAux]
  rw [stepAux_discard _ (auxiliaries_nodup k)]
  simp only [Bool.false_or, TM2.stepAux]
  simp only [auxiliaryBusy]
  by_cases hb : (auxiliaries k).any (fun s => (store s).head?.isSome) = true
  · simp only [hb, Bool.cond_true, ↓reduceIte]
  · have hf := Bool.eq_false_iff.mpr hb
    simp only [hf, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]

/-- No auxiliary is busy precisely when all of them are empty. -/
private theorem auxiliaryBusy_eq_false_iff (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryBusy store = false ↔ ∀ s ∈ auxiliaries k, store s = [] := by
  simp [auxiliaryBusy, List.any_eq_false]

/-- Zero auxiliary storage is equivalent to emptiness of every auxiliary stack. -/
theorem auxiliaryLength_eq_zero_iff (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryLength store = 0 ↔ ∀ s ∈ auxiliaries k, store s = [] := by
  simp [auxiliaryLength, Finset.sum_eq_zero_iff]

/-- Popping auxiliary stacks cannot increase their total length. -/
private theorem auxiliaryLength_popped_le (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryLength (poppedStore (auxiliaries k) store) ≤ auxiliaryLength store := by
  apply Finset.sum_le_sum
  intro s hs
  by_cases h : s ∈ auxiliaries k
  · simp only [poppedStore, h, ↓reduceIte, List.length_tail]
    exact Nat.sub_le _ _
  · simp [h]

/-- A busy round strictly decreases auxiliary storage. -/
private theorem auxiliaryLength_popped_lt (store : ∀ s : Stack k, List (Alphabet s))
    (hb : auxiliaryBusy store = true) :
    auxiliaryLength (poppedStore (auxiliaries k) store) < auxiliaryLength store := by
  have hex : ∃ s, s ∈ auxiliaries k ∧ store s ≠ [] := by
    by_contra! h
    have := (auxiliaryBusy_eq_false_iff store).2 h
    simp [hb] at this
  obtain ⟨s, hs, hne⟩ := hex
  apply Finset.sum_lt_sum
  · intro t ht
    by_cases h : t ∈ auxiliaries k
    · simp only [poppedStore, h, ↓reduceIte, List.length_tail]
      exact Nat.sub_le _ _
    · simp [h]
  · refine ⟨s, Finset.mem_univ s, ?_⟩
    simp only [poppedStore, hs, ↓reduceIte, List.length_tail]
    have : 0 < (store s).length := List.length_pos_iff.mpr hne
    omega

/-- A quiet round leaves every stack unchanged. -/
private theorem poppedStore_eq_of_not_busy (store : ∀ s : Stack k, List (Alphabet s))
    (hb : auxiliaryBusy store = false) : poppedStore (auxiliaries k) store = store := by
  funext s
  by_cases h : s ∈ auxiliaries k
  · simp [poppedStore, h, (auxiliaryBusy_eq_false_iff store).mp hb s h]
  · simp [poppedStore, h]

variable [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)

/-- Reversal transfers one symbol, or resets finite control and halts on the empty stack. -/
private theorem stepAux_reverse (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux (program q₀ transition .reverse) v store =
      match store .reversed with
      | [] => ⟨none, initialControl q₀, Function.update store .reversed []⟩
      | b :: bs => ⟨some .reverse, { v with symbol := some b },
          Function.update (Function.update store .reversed bs) .output (b :: store .output)⟩ := by
  cases h : store .reversed with
  | nil => simp [program, TM2.stepAux, h, Option.isSome, Option.getD]
  | cons b bs =>
    simp only [program, TM2.stepAux, h, List.head?_cons, List.tail_cons,
      Option.isSome, Bool.cond_true]
    rfl

/-- When the auxiliaries are empty, the last reversal step has the canonical halting shape. -/
private theorem stepAux_reverse_nil (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s))
    (ha : ∀ s ∈ auxiliaries k, store s = []) (hr : store .reversed = []) :
    TM2.stepAux (program q₀ transition .reverse) v store =
      haltList (machine q₀ transition) (store .output) := by
  rw [stepAux_reverse, hr]
  change TM2.Cfg.mk none (initialControl q₀) _ = TM2.Cfg.mk none (initialControl q₀) _
  congr 1
  funext s
  cases s with
  | input => simp [machine, ha .input (by simp)]
  | before => simp [machine, ha .before (by simp)]
  | output => rfl
  | reversed => simp [machine]
  | work i b => simp [machine, ha (.work i b) (by simp)]

/-- Reversal preserves already populated output, which becomes a suffix of the final word. -/
private def reverseEvals (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s))
    (ha : ∀ s ∈ auxiliaries k, store s = []) :
    StateTransition.EvalsToInTime (TM2.step (program q₀ transition))
      ⟨some .reverse, v, store⟩
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (store .reversed).reverse (store .output))))
      ((store .reversed).length + 1) := by
  cases hr : store .reversed with
  | nil =>
    have hs : (TM2.step (program q₀ transition)) ⟨some .reverse, v, store⟩ =
        some (haltList (machine q₀ transition) (store .output)) := by
      change some (TM2.stepAux (program q₀ transition .reverse) v store) = _
      exact congrArg some (stepAux_reverse_nil q₀ transition v store ha hr)
    change StateTransition.EvalsToInTime _ _
      (some (haltList (machine q₀ transition) (store .output))) 1
    exact .cons hs (.refl _ _)
  | cons b bs =>
    let store' := Function.update (Function.update store .reversed bs) .output (b :: store .output)
    have ha' : ∀ s ∈ auxiliaries k, store' s = [] := by
      intro s hs
      have hne := (mem_auxiliaries s).mp hs
      simpa only [store', Function.update_of_ne hne.1, Function.update_of_ne hne.2] using ha s hs
    have hs : (TM2.step (program q₀ transition)) ⟨some .reverse, v, store⟩ =
        some ⟨some .reverse, { v with symbol := some b }, store'⟩ := by
      change some (TM2.stepAux (program q₀ transition .reverse) v store) = _
      rw [stepAux_reverse, hr]
    have hrec := reverseEvals { v with symbol := some b } store' ha'
    have hrev : store' .reversed = bs := by simp [store']
    have hout : store' .output = b :: store .output := by
      dsimp only [store']
      exact Function.update_self _ _ _
    rw [hrev, hout] at hrec
    rw [List.reverse_cons]
    have hw : List.append (α := Bool) (bs.reverse ++ [b]) (store .output) =
        List.append (α := Bool) bs.reverse (b :: store .output) :=
      List.append_assoc (α := Bool) bs.reverse [b] (store .output)
    rw [hw]
    change StateTransition.EvalsToInTime _ _ _ (bs.length + 1 + 1)
    exact .cons hs hrec
termination_by (store .reversed).length
decreasing_by simp_wf; rw [hr]; exact Nat.lt_succ_self _

/-- Cleanup reaches the canonical halting configuration within a linear number of TM2 steps. -/
private def cleanEvals (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    StateTransition.EvalsToInTime (TM2.step (program q₀ transition))
      ⟨some .clean, v, store⟩
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (store .reversed).reverse (store .output))))
      (auxiliaryLength store + (store .reversed).length + 2) := by
  cases hb : auxiliaryBusy store with
  | false =>
    have ha := (auxiliaryBusy_eq_false_iff store).mp hb
    have hs : (TM2.step (program q₀ transition)) ⟨some .clean, v, store⟩ =
        some ⟨some .reverse, { v with busy := false }, store⟩ := by
      change some (TM2.stepAux clean v store) = _
      rw [stepAux_clean, hb, poppedStore_eq_of_not_busy store hb]
      rfl
    exact (StateTransition.EvalsToInTime.cons hs (reverseEvals q₀ transition _ store ha)).mono
      (by omega)
  | true =>
    let store' := poppedStore (auxiliaries k) store
    have hrev : store' .reversed = store .reversed := by simp [store', poppedStore]
    have hout : store' .output = store .output := by simp [store', poppedStore]
    have hs : (TM2.step (program q₀ transition)) ⟨some .clean, v, store⟩ =
        some ⟨some .clean, { v with busy := true }, store'⟩ := by
      change some (TM2.stepAux clean v store) = _
      rw [stepAux_clean, hb]
      rfl
    have hrec := cleanEvals { v with busy := true } store'
    rw [hrev, hout] at hrec
    have hlt := auxiliaryLength_popped_lt store hb
    exact (StateTransition.EvalsToInTime.cons hs hrec).mono (by dsimp only [store'] at *; omega)
termination_by auxiliaryLength store
decreasing_by exact auxiliaryLength_popped_lt store hb

/-- Configuration form of `cleanEvals`, allowing arbitrary finite control and stack contents. -/
def cleanupEvals (cfg : (machine q₀ transition).Cfg) (hl : cfg.l = some .clean) :
    StateTransition.EvalsToInTime (machine q₀ transition).step cfg
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (cfg.stk .reversed).reverse (cfg.stk .output))))
      (auxiliaryLength cfg.stk + (cfg.stk .reversed).length + 2) := by
  cases cfg with | mk l v store =>
    cases hl
    exact cleanEvals q₀ transition v store

end
end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Resource bounds for the reverse TM2 compiler

Input storage and the output buffer count toward the target clock. Each source step adds at most
one symbol to the work storage of each simulated tape.

## Main results

* `Turing.MultiTapeTM.ToTM2.outputsInTime`: output correspondence with a linear simulation clock.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

private def stackEquiv (k : ℕ) : Stack k ≃ ((Bool ⊕ Bool) ⊕ Fin k × Bool) where
  toFun
    | .input => .inl (.inl false)
    | .before => .inl (.inl true)
    | .output => .inl (.inr false)
    | .reversed => .inl (.inr true)
    | .work i b => .inr (i, b)
  invFun
    | .inl (.inl false) => .input
    | .inl (.inl true) => .before
    | .inl (.inr false) => .output
    | .inl (.inr true) => .reversed
    | .inr (i, b) => .work i b
  left_inv s := by cases s with | work i b => cases b <;> rfl | _ => rfl
  right_inv s := by
    rcases s with ((b | b) | ⟨i, b⟩) <;> cases b <;> rfl

private theorem sum_stack (f : Stack k → ℕ) :
    ∑ s, f s = f .input + f .before + f .output + f .reversed +
      ∑ i, (f (.work i false) + f (.work i true)) := by
  rw [← (stackEquiv k).symm.sum_comp f]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, stackEquiv,
    Equiv.symm_mk, Equiv.coe_fn_mk]
  simp [add_comm, add_assoc]

/-- Stack storage at a source-step boundary, including the input and output. -/
private theorem totalStackLength_encode (d : Data k State) :
    totalStackLength (encode d) = d.input.left.length + d.input.right.length +
      (∑ i, ((d.work i).left.length + (d.work i).right.length)) + d.output.length := by
  rw [totalStackLength, sum_stack]
  simp only [encode, store, List.length_nil, List.length_reverse]
  omega

/-- Auxiliary storage excludes the accumulated output. -/
private theorem auxiliaryLength_store (d : Data k State) :
    auxiliaryLength (store d) = d.input.left.length + d.input.right.length +
      ∑ i, ((d.work i).left.length + (d.work i).right.length) := by
  have h := totalStackLength_encode d
  rw [totalStackLength_eq] at h
  simp only [encode, store, List.length_reverse, List.length_nil, Nat.add_zero] at h
  omega

private theorem auxiliaryLength_run_time_le (tm : MultiTapeTM k Bool State)
    (input : List Bool) (t : ℕ) :
    auxiliaryLength (store (Data.run tm input t)) ≤ input.length + k * (t + 1) := by
  rw [auxiliaryLength_store, Data.input_length_run]
  have hlocal (i : Fin k) : ((Data.run tm input t).work i).left.length +
      ((Data.run tm input t).work i).right.length ≤ t := by
    induction t with
    | zero => simp [Data.run_zero, Data.init, RawTape.init]
    | succ t ih =>
      rw [Data.run_succ]
      let q := Data.run tm input t
      change ((Data.totalStep tm q).work i).left.length +
        ((Data.totalStep tm q).work i).right.length ≤ t + 1
      cases hs : q.state with
      | none =>
        rw [Data.totalStep_of_halt tm hs]
        exact ih.trans (Nat.le_succ t)
      | some st =>
        rw [Data.totalStep_of_state tm hs]
        let a := tm.tr st q.input.read (fun i => (q.work i).head)
        have h := RawTape.span_step_le (q.work i) (a.workTapes i)
        change ((q.work i).step (a.workTapes i)).left.length +
          ((q.work i).step (a.workTapes i)).right.length ≤ t+1
        dsimp only [RawTape.span] at h
        change (q.work i).left.length + (q.work i).right.length ≤ t at ih
        omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact Nat.add_le_add_left (hsum.trans (Nat.mul_le_mul_left k (Nat.le_succ t))) _

/-- Once the source has halted, its raw output is the complete computed output. -/
private theorem output_run_of_halt (tm : MultiTapeTM k Bool State) {input output : List Bool}
    (hc : tm.Computes input output) {t : ℕ} (ht : (Data.run tm input t).state = none) :
    (Data.run tm input t).output = output := by
  obtain ⟨u, hu, hout⟩ := hc
  have hou : (Data.run tm input u).output = output := (Data.output_run tm input u).trans hout
  rcases le_total t u with htu | hut
  · rwa [Data.run_eq_of_halt tm input htu ht] at hou
  · rw [Data.run_eq_of_halt tm input hut ((Data.state_run tm input u).trans hu), hou]

/-- A native computation is simulated with a linear clock, including clearing every auxiliary
stack, reversing its output and restoring Mathlib's canonical halting control. -/
def outputsInTime [Fintype State] (tm : MultiTapeTM k Bool State)
    {input output : List Bool} {t : ℕ} (hc : tm.Computes input output)
    (ht : tm.RunsInTime input t) :
    TM2OutputsInTime (machine tm.q₀ tm.tr) input (some output)
      (input.length + (k + 1) * (t + 1) + output.length + 3) := by
  classical
  let hex := exists_haltsAt (runsInTime_iff_halted.mp ht)
  let u := hex.choose
  have hu := hex.choose_spec
  let d := Data.run tm input u
  have hd : d.state = none := (Data.state_run tm input u).trans hu.2.halted
  have ho : d.output = output := output_run_of_halt tm hc hd
  let cfg : (machine tm.q₀ tm.tr).Cfg :=
    ⟨some .clean, control d d.input.right.head? false, store d⟩
  have hstep : (machine tm.q₀ tm.tr).step (encode d) = some cfg := step_encode_halt tm d hd
  have hclean := cleanupEvals tm.q₀ tm.tr cfg rfl
  have htail := StateTransition.EvalsToInTime.cons hstep hclean
  change StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step (encode d)
    (some (haltList (machine tm.q₀ tm.tr) (d.output.reverse.reverse ++ [])))
    (auxiliaryLength (store d) + d.output.reverse.length + 2 + 1) at htail
  have htail' : StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step (encode d)
      (some (haltList (machine tm.q₀ tm.tr) output))
      (auxiliaryLength (store d) + d.output.length + 3) := by
    simpa only [cfg, store, List.reverse_reverse, List.append_nil, List.length_reverse,
      Nat.add_assoc, Nat.reduceAdd, ho] using htail
  have hresult := StateTransition.EvalsToInTime.trans (machine tm.q₀ tm.tr).step
    u (auxiliaryLength (store d) + d.output.length + 3) _ _ _
    (prefixEvals tm input hu.2 le_rfl) htail'
  refine hresult.mono ?_
  have ha := auxiliaryLength_run_time_le tm input u
  have hm : k * (u + 1) ≤ k * (t + 1) := Nat.mul_le_mul_left k (by omega)
  dsimp only [d] at *
  rw [ho]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- Terminating native computation yields terminating canonical TM2 computation. -/
def outputs [Fintype State] (tm : MultiTapeTM k Bool State) {input output : List Bool}
    (hc : tm.Computes input output) : TM2Outputs (machine tm.q₀ tm.tr) input (some output) :=
  (outputsInTime tm hc (runsInTime_iff_halted.mpr hc.choose_spec.1)).toTM2Outputs

end

end Turing.MultiTapeTM.ToTM2

namespace Turing.MultiTapeTM

open Polynomial

/-- A native polynomial-time binary multi-tape computation gives a Mathlib TM2
certificate with the same input and output encodings. -/
theorem computableInPolyTime_to_tm2 {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (h : ComputableInPolyTime f encIn encOut) :
    Nonempty (TM2ComputableInPolyTime encIn encOut f) := by
  obtain ⟨t, s, ht, _, k, State, hfinite, tm, htm⟩ := h
  obtain ⟨c, d, ht⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  let : Fintype State := Fintype.ofFinite State
  let p : Polynomial ℕ := X + C (k+2) * (C c * (X + 1)^d + 1) + C 3
  refine ⟨{ tm := ToTM2.machine tm.q₀ tm.tr
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := p
            outputsFun := ?_ }⟩
  intro a
  let n := (encIn a).length
  have hOut : (encOut (f a)).length ≤ t n := by
    have h := (htm a).length_output_le
    exact h
  have hrun := ToTM2.outputsInTime tm (htm a).1 (htm a).2.1
  have htime : n + (k+1) * (t n + 1) + (encOut (f a)).length + 3 ≤ p.eval n := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    have hlinear := Nat.mul_le_mul_left (k+2) (Nat.succ_le_succ (ht n))
    simp only [Nat.add_mul, Nat.succ_eq_add_one, Nat.one_mul] at hlinear ⊢
    omega
  change TM2OutputsInTime (ToTM2.machine tm.q₀ tm.tr) (List.map id (encIn a))
    (some (List.map id (encOut (f a)))) (p.eval n)
  rw [List.map_id, List.map_id]
  exact hrun.mono htime

end Turing.MultiTapeTM

namespace CNFEncComplexity

open Turing.MultiTapeTM
open NeighborInput

private theorem directEncoding_eq (x : ℕ × ℕ × ℕ × ℕ) :
    directEncoding x = encPair encNat (encPair encNat (encPair encNat encNat)) x := by
  simp [directEncoding, encPair_apply, packedBits, frame, binWord_eq_natBits,
    encNat_apply, List.append_assoc]

private def neighborOutput : Option ℕ ↪ List Bool :=
  ⟨encOptNat, by
    intro x y heq
    cases x <;> cases y <;> simp [encOptNat, binWord_eq_natBits] at heq ⊢
    exact encNat.injective (by simpa [encNat_apply] using heq)⟩

private theorem teutsch_output_encoding (P : TimeSpaceMA.Program) (e C a : ℕ) :
    ComputableInPolyTime
      (mergeNbr (fun N => a * (Nat.log 2 N + 1)^a) (ramFoldedLayer P e C))
      (encPair encNat (encPair encNat (encPair encNat encNat))) neighborOutput := by
  apply ComputableInPolyTime.of_tidy
  apply (teutschNbr_tidy P e C a (TimeSpaceMA.shortRun_polytime P)
    TimeSpaceMA.sparseRead_polytime).of_enc_eq
  intro x
  let result := mergeNbr (fun N => a * (Nat.log 2 N + 1)^a) (ramFoldedLayer P e C) x
  change encOptNat result =
    match result with
    | none => [false]
    | some label => true :: label.bits
  cases result <;> simp [encOptNat, binWord_eq_natBits]

end CNFEncComplexity

open CNFEncComplexity Turing.MultiTapeTM

theorem solution (P : TimeSpaceMA.Program) (e C a : ℕ)
    (_hP : P.CoinFree) :
    Nonempty (Turing.TM2ComputableInPolyTime encNbrIn encOptNat
      (mergeNbr (fun N => a * (Nat.log 2 N + 1)^a) (ramFoldedLayer P e C))) := by
  obtain ⟨pre⟩ := NeighborInput.neighborInput_polytime
  obtain ⟨post⟩ := computableInPolyTime_to_tm2 (teutsch_output_encoding P e C a)
  have pre' : Turing.TM2ComputableInPolyTime encNbrIn
      (encPair encNat (encPair encNat (encPair encNat encNat))) id := by
    have he : NeighborInput.directEncoding =
        (encPair encNat (encPair encNat (encPair encNat encNat)) : (ℕ × ℕ × ℕ × ℕ) ↪ List Bool) :=
      funext directEncoding_eq
    rw [← he]
    exact pre
  have result := Turing.TM2ComputableInPolyTime.comp_of_polytime pre' post
  change Nonempty (Turing.TM2ComputableInPolyTime encNbrIn encOptNat
    ((mergeNbr (fun N => a * (Nat.log 2 N + 1)^a) (ramFoldedLayer P e C)) ∘ id)) at result
  simpa only [Function.comp_id] using result
