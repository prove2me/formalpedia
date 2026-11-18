-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.stack_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T17:09:15.085076+00:00
-- url     : https://prove2.me/submissions/a1991fc3-b5d3-4d1d-8938-4cb90df3bf99

import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution

noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackTape

variable {K : Type} {Γ : K → Type} {b : ℕ}

/-- One-hot symbol slots in a fixed-width block; unused blocks are all false. -/
noncomputable def tapeBit (e : (Sigma Γ) ≃ Fin b) (S : ∀ k, List (Γ k)) (p : ℕ) : Bool :=
  if hr : p % (b + 1) < b then
    let x := e.symm ⟨p % (b + 1), hr⟩
    decide ((S x.1)[p / (b + 1)]? = some x.2)
  else false

 theorem read_cell (e : (Sigma Γ) ≃ Fin b) (S : ∀ k, List (Γ k)) (j : ℕ) (x : Sigma Γ) :
    tapeBit e S (j * (b + 1) + (e x).val) = decide ((S x.1)[j]? = some x.2) := by
  have hslot : (e x).val < b + 1 := (e x).isLt.trans (Nat.lt_succ_self _)
  have hmod : (j * (b + 1) + (e x).val) % (b + 1) = (e x).val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hslot]
  have hdiv : (j * (b + 1) + (e x).val) / (b + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_succ b), Nat.div_eq_of_lt hslot, Nat.zero_add]
  have hr : (j * (b + 1) + (e x).val) % (b + 1) < b := by rw [hmod]; exact (e x).isLt
  have he : e.symm ⟨(j * (b + 1) + (e x).val) % (b + 1), hr⟩ = x := by
    calc
      _ = e.symm (e x) := congrArg e.symm (Fin.ext hmod)
      _ = x := e.symm_apply_apply x
  unfold tapeBit
  rw [dif_pos hr]
  simp only [hdiv]
  exact congrArg (fun z : Sigma Γ => decide ((S z.1)[j]? = some z.2)) he

 theorem tape_injective (e : (Sigma Γ) ≃ Fin b) : Function.Injective (tapeBit e) := by
  intro S T h
  funext k
  apply List.ext_getElem?
  intro j
  apply Option.ext
  intro γ
  have hh := congrFun h (j * (b + 1) + (e ⟨k,γ⟩).val)
  simp only [read_cell] at hh
  simpa only [Option.mem_def, eq_comm] using (decide_eq_decide.mp hh)

 theorem beyond_false (e : (Sigma Γ) ≃ Fin b) (S : ∀ k, List (Γ k)) (bound p : ℕ)
    (hbound : ∀ k, (S k).length ≤ bound) (hp : bound ≤ p / (b + 1)) : tapeBit e S p = false := by
  unfold tapeBit
  split_ifs with hr
  · dsimp
    have hlen := (hbound (e.symm ⟨p % (b + 1), hr⟩).1).trans hp
    simp [List.getElem?_eq_none hlen]
  · rfl

 theorem empty_tape (e : (Sigma Γ) ≃ Fin b) : tapeBit e (fun _ => []) = fun _ => false := by
  funext p
  exact beyond_false e (fun _ => []) 0 p (fun _ => Nat.le_refl _) (Nat.zero_le _)

end EdgeSublinearMWIS.Main.StackTape
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackSpace

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

 def cost : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => cost q + 1
  | .peek _ _ q => cost q + 1
  | .pop _ _ q => cost q + 1
  | .load _ q => cost q + 1
  | .branch _ q r => max (cost q) (cost r) + 1
  | .goto _ => 1
  | .halt => 1

 theorem cost_pos (q : Turing.TM2.Stmt Γ Λ σ) : 0 < cost q := by cases q <;> simp [cost]

 def space [Fintype K] (S : ∀ k, List (Γ k)) : ℕ := ∑ k, (S k).length

 theorem space_update [Fintype K] [DecidableEq K] (S : ∀ k, List (Γ k)) (k : K) (L : List (Γ k)) :
    space (Function.update S k L) + (S k).length = space S + L.length := by
  have heq : (fun j => (Function.update S k L j).length) = Function.update (fun j => (S j).length) k L.length := by
    funext j
    by_cases h : j = k
    · subst j; simp
    · simp [Function.update, h]
  unfold space
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add (s := Finset.univ) (fun j => (S j).length) (Finset.mem_univ k)
  omega

 theorem stepAux_space [Fintype K] [DecidableEq K] (q : Turing.TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    space (Turing.TM2.stepAux q v S).stk ≤ space S + cost q := by
  induction q generalizing v S with
  | push k f q ih =>
    have hh := ih v (Function.update S k (f v :: S k))
    have hu := space_update S k (f v :: S k)
    simp only [List.length_cons] at hu
    change space (Turing.TM2.stepAux q v (Function.update S k (f v :: S k))).stk ≤ space S + (cost q + 1)
    omega
  | peek k f q ih =>
    have hh := ih (f v (S k).head?) S
    change space (Turing.TM2.stepAux q (f v (S k).head?) S).stk ≤ space S + (cost q + 1)
    omega
  | pop k f q ih =>
    have hh := ih (f v (S k).head?) (Function.update S k (S k).tail)
    have hu := space_update S k (S k).tail
    have hl : (S k).tail.length ≤ (S k).length := by simp only [List.length_tail]; omega
    change space (Turing.TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail)).stk ≤ space S + (cost q + 1)
    omega
  | load f q ih =>
    have hh := ih (f v) S
    change space (Turing.TM2.stepAux q (f v) S).stk ≤ space S + (cost q + 1)
    omega
  | branch f q r ihq ihr =>
    change space (cond (f v) (Turing.TM2.stepAux q v S) (Turing.TM2.stepAux r v S)).stk ≤ space S + (max (cost q) (cost r) + 1)
    cases hv : f v with
    | false => simp only [cond_false]; have hh := ihr v S; have hm := le_max_right (cost q) (cost r); omega
    | true => simp only [cond_true]; have hh := ihq v S; have hm := le_max_left (cost q) (cost r); omega
  | goto f => simp [Turing.TM2.stepAux, cost]
  | halt => simp [Turing.TM2.stepAux, cost]

 def bound (tm : Turing.FinTM2) : ℕ := Finset.univ.sup (fun l => cost (tm.m l))

 theorem cost_le_bound (tm : Turing.FinTM2) (l : tm.Λ) : cost (tm.m l) ≤ bound tm := by
  unfold bound
  exact Finset.le_sup (f := fun l => cost (tm.m l)) (Finset.mem_univ l)

 theorem bound_pos (tm : Turing.FinTM2) : 0 < bound tm :=
  (cost_pos (tm.m tm.main)).trans_le (cost_le_bound tm tm.main)

 theorem initial_space (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) :
    space (Turing.initList tm input).stk = input.length := by
  have hlen (k : tm.K) : ((Turing.initList tm input).stk k).length = if k = tm.k₀ then input.length else 0 := by
    by_cases h : k = tm.k₀
    · subst k; simp [Turing.initList]
    · simp [Turing.initList, h]
  unfold space
  simp only [hlen]
  simp

 set_option backward.isDefEq.respectTransparency.types false in
 theorem step_space (tm : Turing.FinTM2) (c c' : tm.Cfg) (h : tm.step c = some c') :
    space c'.stk ≤ space c.stk + bound tm := by
  letI : DecidableEq tm.K := tm.decidableEqK
  change Turing.TM2.step tm.m c = some c' at h
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [Turing.FinTM2.step, Turing.TM2.step] at h
  | some l =>
    change some (Turing.TM2.stepAux (tm.m l) v S) = some c' at h
    have heq := Option.some.inj h
    rw [← heq]
    exact (stepAux_space (tm.m l) v S).trans (Nat.add_le_add_left (cost_le_bound tm l) _)

 def run (tm : Turing.FinTM2) (start : tm.Cfg) : ℕ → Option tm.Cfg
  | 0 => some start
  | t + 1 => (run tm start t).bind tm.step

 theorem run_space (tm : Turing.FinTM2) (start : tm.Cfg) (t : ℕ) (c : tm.Cfg)
    (h : run tm start t = some c) : space c.stk ≤ space start.stk + bound tm * t := by
  induction t generalizing c with
  | zero => simp only [run, Option.some.injEq] at h; subst c; simp
  | succ t ih =>
    cases he : run tm start t with
    | none => simp only [run, he, Option.bind_none, reduceCtorEq] at h
    | some prev =>
      have hstep : tm.step prev = some c := by simpa only [run, he, Option.bind_some] using h
      have hi := ih prev he
      have hs := step_space tm prev c hstep
      rw [Nat.mul_succ]
      omega

 theorem input_run_space (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (t : ℕ) (c : tm.Cfg)
    (h : run tm (Turing.initList tm input) t = some c) : space c.stk ≤ input.length + bound tm * t := by
  simpa only [initial_space] using run_space tm (Turing.initList tm input) t c h

 theorem stack_length_le_space [Fintype K] (S : ∀ k, List (Γ k)) (k : K) : (S k).length ≤ space S := by
  unfold space
  exact Finset.single_le_sum (f := fun j => (S j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

end EdgeSublinearMWIS.Main.StackSpace
end

noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

noncomputable instance alphabetFintype (P : EdgeSublinearMWIS.Main.Program) (k : P.machine.tm.K) :
    Fintype (P.machine.tm.Γ k) := @Fintype.ofFinite _ (P.finiteAlphabet k)

noncomputable def allStatements (P : EdgeSublinearMWIS.Main.Program) : Finset P.machine.tm.Stmt :=
  Finset.univ.biUnion (fun l => Turing.TM2.stmts₁ (P.machine.tm.m l))

abbrev Statement (P : EdgeSublinearMWIS.Main.Program) := {q // q ∈ allStatements P}

abbrev Resume (P : EdgeSublinearMWIS.Main.Program) := Statement P × P.machine.tm.σ

noncomputable def alphabetCode (P : EdgeSublinearMWIS.Main.Program) :
    (Sigma P.machine.tm.Γ) ≃ Fin (Fintype.card (Sigma P.machine.tm.Γ)) := Fintype.equivFin _

noncomputable def blockSize (P : EdgeSublinearMWIS.Main.Program) : ℕ := Fintype.card (Sigma P.machine.tm.Γ) + 1

 theorem blockSize_pos (P : EdgeSublinearMWIS.Main.Program) : 0 < blockSize P := Nat.zero_lt_succ _

 theorem main_mem (P : EdgeSublinearMWIS.Main.Program) (l : P.machine.tm.Λ) :
    P.machine.tm.m l ∈ allStatements P := by
  exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Turing.TM2.stmts₁_self⟩

noncomputable instance resumeFintype (P : EdgeSublinearMWIS.Main.Program) : Fintype (Resume P) := inferInstance

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.FiniteBitControl

/-- A typed presentation of the same local finite-table instruction. -/
structure Instruction (Q : Type) where
  next : Option Q
  workWrite : Bool
  catalystWrite : Option Bool
  inputMove : Move
  workMove : Move
  catalystMove : Move
  emit : Option Bool

structure Configuration (Q : Type) where
  state : Option Q
  inputHead : ℕ
  workHead : ℕ
  catalystHead : ℕ
  work : ℕ → Bool
  catalyst : List Bool
  output : List Bool

abbrev Table (Q : Type) := Q → Option Bool → Bool → Option Bool → Bool → Bool → Bool → Instruction Q

noncomputable def machine {Q : Type} [Fintype Q] (start : Q) (table : Table Q) : Machine where
  states := Fintype.card Q
  start := Fintype.equivFin Q start
  table q i w c io wo co :=
    let a := table ((Fintype.equivFin Q).symm q) i w c io wo co
    ⟨a.next.map (Fintype.equivFin Q), a.workWrite, a.catalystWrite,
      a.inputMove, a.workMove, a.catalystMove, a.emit⟩

noncomputable def encode {Q : Type} [Fintype Q] (start : Q) (table : Table Q)
    (c : Configuration Q) : CatalyticMatching.General.Configuration (machine start table) :=
  ⟨c.state.map (Fintype.equivFin Q), c.inputHead, c.workHead, c.catalystHead,
    c.work, c.catalyst, c.output⟩

def step {Q : Type} (table : Table Q) (input : List Bool) (c : Configuration Q) : Option (Configuration Q) :=
  match c.state with
  | none => some c
  | some q =>
    let a := table q (if c.inputHead = 0 then none else input[c.inputHead - 1]?)
      (c.work c.workHead) c.catalyst[c.catalystHead]?
      (c.inputHead == 0) (c.workHead == 0) (c.catalystHead == 0)
    if a.inputMove.apply c.inputHead ≤ input.length + 1 ∧
        a.catalystMove.apply c.catalystHead ≤ c.catalyst.length ∧
        (a.catalystWrite.isSome → c.catalystHead < c.catalyst.length) then
      some ⟨a.next, a.inputMove.apply c.inputHead, a.workMove.apply c.workHead,
        a.catalystMove.apply c.catalystHead,
        Function.update c.work c.workHead a.workWrite,
        (match a.catalystWrite with
          | none => c.catalyst
          | some b => c.catalyst.set c.catalystHead b),
        c.output ++ a.emit.toList⟩
    else none

 set_option backward.isDefEq.respectTransparency.types false in
 theorem step_encode {Q : Type} [Fintype Q] (start : Q) (table : Table Q) (input : List Bool)
    (c : Configuration Q) :
    (step table input c).map (encode start table) = (machine start table).step input (encode start table c) := by
  rcases c with ⟨state, ih, wh, ch, work, cat, out⟩
  cases state with
  | none => rfl
  | some q =>
    simp only [step, machine, encode, Machine.step, Option.map_some, Equiv.symm_apply_apply]
    split_ifs <;> simp_all [encode, Option.map] <;> rfl

 def initial {Q : Type} (start : Q) (catalyst : List Bool) : Configuration Q :=
  ⟨some start, 0, 0, 0, fun _ => false, catalyst, []⟩

 def run {Q : Type} (start : Q) (table : Table Q) (input catalyst : List Bool) : ℕ → Option (Configuration Q)
  | 0 => some (initial start catalyst)
  | t + 1 => (run start table input catalyst t).bind (step table input)

 theorem run_encode {Q : Type} [Fintype Q] (start : Q) (table : Table Q) (input catalyst : List Bool) (t : ℕ) :
    (run start table input catalyst t).map (encode start table) = (machine start table).run input catalyst t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run, Machine.run, ← ih]
    cases he : run start table input catalyst t with
    | none => rfl
    | some c => simpa only [Option.bind_some, Option.map_some] using step_encode start table input c

 theorem encode_output {Q : Type} [Fintype Q] (start : Q) (table : Table Q) (c : Configuration Q) :
    (encode start table c).output = c.output := rfl

 theorem encode_state_none {Q : Type} [Fintype Q] (start : Q) (table : Table Q) (c : Configuration Q) :
    (encode start table c).state = none ↔ c.state = none := by
  cases hs : c.state <;> simp only [encode, hs, Option.map, reduceCtorEq, iff_self]

def runFrom {Q : Type} (table : Table Q) (input : List Bool) (c : Configuration Q) : ℕ → Option (Configuration Q)
  | 0 => some c
  | t + 1 => (runFrom table input c t).bind (step table input)

theorem runFrom_add {Q : Type} (table : Table Q) (input : List Bool)
    (c : Configuration Q) (s t : ℕ) :
    runFrom table input c (s+t) = (runFrom table input c s).bind (fun d => runFrom table input d t) := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [show s + (t+1) = (s+t)+1 by omega, runFrom, ih]
    cases runFrom table input c s <;> rfl

theorem runFrom_trans {Q : Type} (table : Table Q) (input : List Bool)
    (c d e : Configuration Q) (s t : ℕ)
    (h : runFrom table input c s = some d) (h' : runFrom table input d t = some e) :
    runFrom table input c (s+t) = some e := by rw [runFrom_add, h]; exact h'

theorem runFrom_initial {Q : Type} (start : Q) (table : Table Q) (input catalyst : List Bool) (t : ℕ) :
    runFrom table input (initial start catalyst) t = run start table input catalyst t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [runFrom, run, ih]

theorem runFrom_halt {Q : Type} (table : Table Q) (input : List Bool) (c : Configuration Q)
    (hc : c.state = none) (t : ℕ) : runFrom table input c t = some c := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [runFrom, ih, Option.bind_some, step, hc]

end EdgeSublinearMWIS.Main.FiniteBitControl
end

noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.CellControl
open CatalyticMatching.General

structure Instruction (Q A : Type) where
  next : Option Q
  write : A
  inputMove : Move := .stay
  workMove : Move := .stay
  emit : Option Bool := none

structure Configuration (Q A : Type) where
  state : Option Q
  inputHead : ℕ
  workHead : ℕ
  work : ℕ → A
  output : List Bool

abbrev Table (Q A : Type) := Q → Option Bool → A → Bool → Bool → Instruction Q A

def step {Q A : Type} (table : Table Q A) (input : List Bool) (c : Configuration Q A) :
    Option (Configuration Q A) :=
  match c.state with
  | none => some c
  | some q =>
    let a := table q (if c.inputHead = 0 then none else input[c.inputHead - 1]?)
      (c.work c.workHead) (c.inputHead == 0) (c.workHead == 0)
    if a.inputMove.apply c.inputHead ≤ input.length + 1 then
      some ⟨a.next, a.inputMove.apply c.inputHead, a.workMove.apply c.workHead,
        Function.update c.work c.workHead a.write, c.output ++ a.emit.toList⟩
    else none

def runFrom {Q A : Type} (table : Table Q A) (input : List Bool) (c : Configuration Q A) :
    ℕ → Option (Configuration Q A)
  | 0 => some c
  | t + 1 => (runFrom table input c t).bind (step table input)

theorem runFrom_add {Q A : Type} (table : Table Q A) (input : List Bool)
    (c : Configuration Q A) (s t : ℕ) :
    runFrom table input c (s+t) = (runFrom table input c s).bind (fun d => runFrom table input d t) := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [show s + (t+1) = (s+t)+1 by omega, runFrom, ih]
    cases runFrom table input c s <;> rfl

theorem runFrom_trans {Q A : Type} (table : Table Q A) (input : List Bool)
    (c d e : Configuration Q A) (s t : ℕ)
    (h : runFrom table input c s = some d) (h' : runFrom table input d t = some e) :
    runFrom table input c (s+t) = some e := by rw [runFrom_add, h]; exact h'

theorem step_input_bound {Q A : Type} (table : Table Q A) (input : List Bool)
    (c d : Configuration Q A) (hi : c.inputHead ≤ input.length+1)
    (hs : step table input c = some d) : d.inputHead ≤ input.length+1 := by
  rcases c with ⟨state,ih,wh,w,out⟩
  cases state with
  | none => have hd := Option.some.inj hs; subst d; exact hi
  | some q =>
    let a := table q (if ih=0 then none else input[ih-1]?) (w wh) (ih==0) (wh==0)
    change (if a.inputMove.apply ih ≤ input.length+1 then
      some (⟨a.next,a.inputMove.apply ih,a.workMove.apply wh,Function.update w wh a.write,out ++ a.emit.toList⟩ : Configuration Q A)
      else none) = some d at hs
    split at hs
    · rename_i hh
      have hd := Option.some.inj hs
      subst d
      exact hh
    · contradiction

end EdgeSublinearMWIS.Main.CellControl
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.CellBitCode

variable {A : Type} [Fintype A] (blank : A)

noncomputable def width : ℕ := Fintype.card A + 1
noncomputable def code (a : A) (i : Fin (width (A := A))) : Bool :=
  decide (a ≠ blank ∧ i.val = (Fintype.equivFin A a).val)

theorem code_blank : code blank blank = fun _ => false := by funext i; simp [code]

theorem code_injective : Function.Injective (code blank) := by
  intro a b hab
  by_cases ha : a = blank
  · subst a
    by_contra hb
    have h := congrFun hab ⟨(Fintype.equivFin A b).val, by dsimp [width]; omega⟩
    simp [code] at h
    exact hb h.symm
  · have h := congrFun hab ⟨(Fintype.equivFin A a).val, by dsimp [width]; omega⟩
    have hh : b ≠ blank ∧ (Fintype.equivFin A a).val = (Fintype.equivFin A b).val := by simpa [code, ha] using h
    have hval := hh.2
    exact (Fintype.equivFin A).injective (Fin.ext hval)

noncomputable def decode (s : Fin (width (A := A)) → Bool) : A :=
  if h : ∃ a, code blank a = s then h.choose else blank

theorem decode_code (a : A) : decode blank (code blank a) = a := by
  unfold decode
  rw [dif_pos ⟨a,rfl⟩]
  exact code_injective blank (Exists.choose_spec (show ∃ b, code blank b = code blank a from ⟨a,rfl⟩))

noncomputable def tape (s : ℕ → A) (p : ℕ) : Bool :=
  code blank (s (p / width (A := A))) ⟨p % width (A := A), Nat.mod_lt _ (by dsimp [width]; omega)⟩

theorem tape_read (s : ℕ → A) (h : ℕ) (i : Fin (width (A := A))) :
    tape blank s (h * width (A := A) + i.val) = code blank (s h) i := by
  have hw : 0 < width (A := A) := by dsimp [width]; omega
  have hd : (h * width (A := A) + i.val) / width (A := A) = h := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  have hm : (h * width (A := A) + i.val) % width (A := A) = i.val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  unfold tape
  simp only [hd]
  exact congrArg (code blank (s h)) (Fin.ext hm)

theorem tape_blank : tape blank (fun _ => blank) = fun _ => false := by
  funext p
  simp [tape, code]

instance moveFintype : Fintype Move :=
  ⟨{.left,.stay,.right}, by intro m; cases m <;> simp⟩

deriving instance Fintype for CellControl.Instruction

inductive State (Q A : Type) [Fintype A] where
  | ready (q : Q)
  | read (q : Q) (origin : Bool) (i : Fin (width (A := A))) (buffer : Fin (width (A := A)) → Bool)
  | rewind (a : CellControl.Instruction Q A) (i : Fin (width (A := A) + 1))
  | write (a : CellControl.Instruction Q A) (i : Fin (width (A := A)))
  | back (a : CellControl.Instruction Q A) (i : Fin (width (A := A) + 1))
  | commit (a : CellControl.Instruction Q A)
  | move (next : Option Q) (direction : Move) (i : Fin (width (A := A) + 1))
  deriving Fintype

noncomputable def instruction {Q : Type} (table : CellControl.Table Q A) :
    FiniteBitControl.Table (State Q A) := fun q inp bit _ io wo _ =>
  match q with
  | .ready q => ⟨some (.read q wo ⟨0,by dsimp [width]; omega⟩ (fun _ => false)), bit, none, .stay, .stay, .stay, none⟩
  | .read q origin i buffer =>
    let buffer' := Function.update buffer i bit
    if hi : i.val + 1 < width (A := A) then
      ⟨some (.read q origin ⟨i.val+1,hi⟩ buffer'), bit, none, .stay, .right, .stay, none⟩
    else
      ⟨some (.rewind (table q inp (decode blank buffer') io origin)
        ⟨width (A := A)-1, by omega⟩), bit, none, .stay, .stay, .stay, none⟩
  | .rewind a i =>
    if i.val = 0 then
      ⟨some (.write a ⟨0,by dsimp [width]; omega⟩), bit, none, .stay, .stay, .stay, none⟩
    else
      ⟨some (.rewind a ⟨i.val-1,by omega⟩), bit, none, .stay, .left, .stay, none⟩
  | .write a i =>
    if hi : i.val+1 < width (A := A) then
      ⟨some (.write a ⟨i.val+1,hi⟩), code blank a.write i, none, .stay, .right, .stay, none⟩
    else
      ⟨some (.back a ⟨width (A := A)-1,by omega⟩), code blank a.write i, none, .stay, .stay, .stay, none⟩
  | .back a i =>
    if i.val = 0 then
      ⟨some (.commit a), bit, none, .stay, .stay, .stay, none⟩
    else
      ⟨some (.back a ⟨i.val-1,by omega⟩), bit, none, .stay, .left, .stay, none⟩
  | .commit a =>
      ⟨some (.move a.next a.workMove ⟨width (A := A),by omega⟩), bit, none, a.inputMove, .stay, .stay, a.emit⟩
  | .move next direction i =>
    if i.val = 0 then
      ⟨next.map .ready, bit, none, .stay, .stay, .stay, none⟩
    else
      ⟨some (.move next direction ⟨i.val-1,by omega⟩), bit, none, .stay, direction, .stay, none⟩

end EdgeSublinearMWIS.Main.CellBitCode
end

noncomputable section

open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BitRoutine
open FiniteBitControl

variable {Q : Type}

def cfg (state : Option Q) (ih wh : ℕ) (w : ℕ → Bool) (out : List Bool) : Configuration Q :=
  ⟨state,ih,wh,0,w,[],out⟩

def act (next : Option Q) (bit : Bool) (im wm : Move) (emit : Option Bool) : Instruction Q :=
  ⟨next,bit,none,im,wm,.stay,emit⟩

theorem step_cfg (table : Table Q) (input : List Bool) (q : Q) (ih wh : ℕ) (w : ℕ → Bool)
    (out : List Bool) (next : Option Q) (bit : Bool) (im wm : Move) (emit : Option Bool)
    (ht : table q (if ih=0 then none else input[ih-1]?) (w wh) none (ih==0) (wh==0) true = act next bit im wm emit)
    (hi : im.apply ih ≤ input.length+1) :
    step table input (cfg (some q) ih wh w out) =
      some (cfg next (im.apply ih) (wm.apply wh) (Function.update w wh bit) (out ++ emit.toList)) := by
  dsimp only [step, cfg]
  simp only [List.getElem?_nil, beq_self_eq_true]
  rw [ht]
  simp only [act, Move.apply] at *
  simp [hi]

theorem preserve (w : ℕ → Bool) (h : ℕ) : Function.update w h (w h) = w := by
  funext j
  by_cases hj : j=h <;> simp [Function.update, hj]

theorem runFrom_succ_first (table : Table Q) (input : List Bool) (c : Configuration Q) (t : ℕ) :
    runFrom table input c (t+1) = (step table input c).bind (fun d => runFrom table input d t) := by
  rw [show t+1=1+t by omega, runFrom_add]
  rfl

theorem left_counter_run (table : Table Q) (input : List Bool) (N : ℕ)
    (r : Fin (N+1) → Q) (next : Option Q) (ih base : ℕ) (w : ℕ → Bool) (out : List Bool)
    (hs : ∀ j : Fin (N+1), step table input (cfg (some (r j)) ih (base+j.val) w out) =
      some (cfg (if j.val=0 then next else some (r ⟨j.val-1,by omega⟩))
        ih (base+(j.val-1)) w out))
    (m : ℕ) (hm : m ≤ N) :
    runFrom table input (cfg (some (r ⟨m,by omega⟩)) ih (base+m) w out) (m+1) =
      some (cfg next ih base w out) := by
  induction m with
  | zero => simpa only [runFrom, Option.bind_some, Nat.zero_add, Nat.add_zero, Nat.sub_self, Nat.zero_sub, ↓reduceIte] using hs ⟨0,by omega⟩
  | succ m ih' =>
    rw [runFrom_succ_first, hs]
    simp only [Nat.add_eq_zero_iff, Nat.succ_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel, Option.bind_some]
    exact ih' (by omega)

end EdgeSublinearMWIS.Main.BitRoutine
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.CellBitCode
open FiniteBitControl BitRoutine
variable {Q A : Type} [Fintype A] (blank : A)

 def readPrefix (v : Fin (width (A := A)) → Bool) (m : ℕ) : Fin (width (A := A)) → Bool :=
  fun j => if j.val < m then v j else false

 theorem readPrefix_update (v : Fin (width (A := A)) → Bool) (i : Fin (width (A := A))) :
    Function.update (readPrefix v i.val) i (v i) = readPrefix v (i.val+1) := by
  funext j
  by_cases h : j=i
  · subst j; simp [readPrefix]
  · have hne : j.val ≠ i.val := fun he => h (Fin.ext he)
    simp only [Function.update_of_ne h, readPrefix]
    by_cases hj : j.val < i.val <;> simp [hj, show (j.val < i.val+1) ↔ j.val < i.val by omega]

 theorem readPrefix_full (v : Fin (width (A := A)) → Bool) : readPrefix v (width (A := A)) = v := by
  funext j; simp [readPrefix, j.isLt]

 theorem read_run (table : CellControl.Table Q A) (input : List Bool)
    (q : Q) (origin : Bool) (ih h : ℕ) (s : ℕ → A) (out : List Bool)
    (hi : ih ≤ input.length+1) (i : Fin (width (A := A))) :
    runFrom (instruction blank table) input
      (cfg (some (.read q origin i (readPrefix (code blank (s h)) i.val))) ih
        (h * width (A := A) + i.val) (tape blank s) out)
      (width (A := A) - i.val) =
    some (cfg (some (.rewind
      (table q (if ih=0 then none else input[ih-1]?) (s h) (ih==0) origin)
      ⟨width (A := A)-1,by omega⟩)) ih
      (h * width (A := A) + (width (A := A)-1)) (tape blank s) out) := by
  by_cases hl : i.val+1 < width (A := A)
  · let j : Fin (width (A := A)) := ⟨i.val+1,hl⟩
    have hs := step_cfg (instruction blank table) input
      (.read q origin i (readPrefix (code blank (s h)) i.val)) ih
      (h * width (A := A) + i.val) (tape blank s) out
      (some (.read q origin j (readPrefix (code blank (s h)) (i.val+1))))
      (tape blank s (h * width (A := A) + i.val)) .stay .right none
      (by simp only [instruction, hl, ↓reduceDIte, tape_read, readPrefix_update, act]; rfl)
      (by simpa only [Move.apply] using hi)
    simp only [Move.apply, preserve, Option.toList_none, List.append_nil] at hs
    rw [show width (A := A)-i.val = (width (A := A)-j.val)+1 by dsimp [j]; omega,
      runFrom_succ_first, hs, Option.bind_some]
    simpa only [j, Nat.add_assoc] using read_run table input q origin ih h s out hi j
  · have hilast : i.val = width (A := A)-1 := by have := i.isLt; omega
    have hup : Function.update (readPrefix (code blank (s h)) i.val) i (code blank (s h) i) = code blank (s h) := by
      rw [readPrefix_update, show i.val+1=width (A := A) by have := i.isLt; omega, readPrefix_full]
    have hs := step_cfg (instruction blank table) input
      (.read q origin i (readPrefix (code blank (s h)) i.val)) ih
      (h * width (A := A) + i.val) (tape blank s) out
      (some (.rewind (table q (if ih=0 then none else input[ih-1]?) (s h) (ih==0) origin)
        ⟨width (A := A)-1,by omega⟩))
      (tape blank s (h * width (A := A) + i.val)) .stay .stay none
      (by simp only [instruction, hl, ↓reduceDIte, tape_read, hup, decode_code]; rfl)
      (by simpa only [Move.apply] using hi)
    rw [show width (A := A)-i.val=1 by have := i.isLt; omega]
    simpa only [runFrom, Option.bind_some, Move.apply, preserve, Option.toList_none,
      List.append_nil, hilast] using hs
termination_by width (A := A) - i.val
 decreasing_by have := i.isLt; omega

end EdgeSublinearMWIS.Main.CellBitCode
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.CellBitCode
open FiniteBitControl BitRoutine
variable {Q A : Type} [Fintype A] (blank : A)

 theorem rewind_run (table : CellControl.Table Q A) (input : List Bool)
    (a : CellControl.Instruction Q A) (ih base : ℕ) (w : ℕ → Bool) (out : List Bool)
    (hi : ih ≤ input.length+1) (m : ℕ) (hm : m ≤ width (A := A)) :
    runFrom (instruction blank table) input
      (cfg (some (.rewind a ⟨m,by omega⟩)) ih (base+m) w out) (m+1) =
      some (cfg (some (.write a ⟨0,by dsimp [width]; omega⟩)) ih base w out) := by
  apply left_counter_run (instruction blank table) input (width (A := A))
    (fun j => .rewind a j) (some (.write a ⟨0,by dsimp [width]; omega⟩)) ih base w out ?_ m hm
  intro j
  by_cases hj : j.val=0
  · have hs := step_cfg (instruction blank table) input (.rewind a j) ih (base+j.val) w out
      (some (.write a ⟨0,by dsimp [width]; omega⟩)) (w (base+j.val)) .stay .stay none
      (by simp only [instruction, hj, ↓reduceIte]; rfl)
      (by simpa only [Move.apply] using hi)
    simpa only [Move.apply, preserve, Option.toList_none, List.append_nil, hj,
      Nat.zero_sub, Nat.add_zero, ↓reduceIte] using hs
  · have hs := step_cfg (instruction blank table) input (.rewind a j) ih (base+j.val) w out
      (some (.rewind a ⟨j.val-1,by omega⟩)) (w (base+j.val)) .stay .left none
      (by simp only [instruction, hj, ↓reduceIte]; rfl)
      (by simpa only [Move.apply] using hi)
    simpa only [Move.apply, preserve, Option.toList_none, List.append_nil, hj,
      ↓reduceIte, show base+j.val-1=base+(j.val-1) by omega] using hs

 theorem back_run (table : CellControl.Table Q A) (input : List Bool)
    (a : CellControl.Instruction Q A) (ih base : ℕ) (w : ℕ → Bool) (out : List Bool)
    (hi : ih ≤ input.length+1) (m : ℕ) (hm : m ≤ width (A := A)) :
    runFrom (instruction blank table) input
      (cfg (some (.back a ⟨m,by omega⟩)) ih (base+m) w out) (m+1) =
      some (cfg (some (.commit a)) ih base w out) := by
  apply left_counter_run (instruction blank table) input (width (A := A))
    (fun j => .back a j) (some (.commit a)) ih base w out ?_ m hm
  intro j
  by_cases hj : j.val=0
  · have hs := step_cfg (instruction blank table) input (.back a j) ih (base+j.val) w out
      (some (.commit a)) (w (base+j.val)) .stay .stay none
      (by simp only [instruction, hj, ↓reduceIte]; rfl)
      (by simpa only [Move.apply] using hi)
    simpa only [Move.apply, preserve, Option.toList_none, List.append_nil, hj,
      Nat.zero_sub, Nat.add_zero, ↓reduceIte] using hs
  · have hs := step_cfg (instruction blank table) input (.back a j) ih (base+j.val) w out
      (some (.back a ⟨j.val-1,by omega⟩)) (w (base+j.val)) .stay .left none
      (by simp only [instruction, hj, ↓reduceIte]; rfl)
      (by simpa only [Move.apply] using hi)
    simpa only [Move.apply, preserve, Option.toList_none, List.append_nil, hj,
      ↓reduceIte, show base+j.val-1=base+(j.val-1) by omega] using hs

end EdgeSublinearMWIS.Main.CellBitCode
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.CellBitCode
open FiniteBitControl BitRoutine
variable {Q A : Type} [Fintype A] (blank : A)

 def patched (s : ℕ → A) (h : ℕ) (a : A) (m p : ℕ) : Bool :=
  if p / width (A := A) = h ∧ p % width (A := A) < m then
    code blank a ⟨p % width (A := A),Nat.mod_lt _ (by dsimp [width]; omega)⟩
  else tape blank s p

 theorem patched_zero (s : ℕ → A) (h : ℕ) (a : A) : patched blank s h a 0 = tape blank s := by
  funext p; simp [patched]

 theorem patched_full (s : ℕ → A) (h : ℕ) (a : A) :
    patched blank s h a (width (A := A)) = tape blank (Function.update s h a) := by
  funext p
  have hm := Nat.mod_lt p (show 0 < width (A := A) by dsimp [width]; omega)
  by_cases hd : p / width (A := A) = h
  · simp only [patched, hd, hm, and_self, ↓reduceIte, tape, Function.update_self]
  · simp only [patched, hd, false_and, ↓reduceIte, tape, Function.update_of_ne hd]

 theorem patched_update (s : ℕ → A) (h : ℕ) (a : A) (i : Fin (width (A := A))) :
    Function.update (patched blank s h a i.val) (h * width (A := A)+i.val) (code blank a i) =
      patched blank s h a (i.val+1) := by
  funext p
  have hw : 0 < width (A := A) := by dsimp [width]; omega
  by_cases hp : p = h*width (A := A)+i.val
  · subst p
    have hd : (h*width (A := A)+i.val)/width (A := A)=h := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
    have hm : (h*width (A := A)+i.val)%width (A := A)=i.val := by
      rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt i.isLt]
    simp only [Function.update_self,patched,hd,hm,lt_add_iff_pos_right,Nat.lt_succ_self,and_self,↓reduceIte]
  · rw [Function.update_of_ne hp]
    by_cases hd : p / width (A := A)=h
    · have hne : p % width (A := A) ≠ i.val := by
        intro he
        have hh := Nat.div_add_mod p (width (A := A))
        rw [hd,he,Nat.mul_comm] at hh
        exact hp hh.symm
      have hl : (p % width (A := A) < i.val+1) ↔ p % width (A := A) < i.val := by omega
      simp only [patched,hd,true_and,hl]
    · simp only [patched,hd,false_and,↓reduceIte]

 theorem write_run (table : CellControl.Table Q A) (input : List Bool)
    (a : CellControl.Instruction Q A) (ih h : ℕ) (s : ℕ → A) (out : List Bool)
    (hi : ih ≤ input.length+1) (i : Fin (width (A := A))) :
    runFrom (instruction blank table) input
      (cfg (some (.write a i)) ih (h * width (A := A)+i.val)
        (patched blank s h a.write i.val) out)
      (width (A := A)-i.val) =
    some (cfg (some (.back a ⟨width (A := A)-1,by omega⟩)) ih
      (h * width (A := A)+(width (A := A)-1)) (tape blank (Function.update s h a.write)) out) := by
  by_cases hl : i.val+1 < width (A := A)
  · let j : Fin (width (A := A)) := ⟨i.val+1,hl⟩
    have hs := step_cfg (instruction blank table) input (.write a i) ih
      (h*width (A := A)+i.val) (patched blank s h a.write i.val) out
      (some (.write a j)) (code blank a.write i) .stay .right none
      (by simp only [instruction,hl,↓reduceDIte]; rfl)
      (by simpa only [Move.apply] using hi)
    simp only [Move.apply,patched_update,Option.toList_none,List.append_nil] at hs
    rw [show width (A := A)-i.val=(width (A := A)-j.val)+1 by dsimp [j]; omega,
      runFrom_succ_first,hs,Option.bind_some]
    simpa only [j,Nat.add_assoc] using write_run table input a ih h s out hi j
  · have hilast : i.val=width (A := A)-1 := by have := i.isLt; omega
    have hs := step_cfg (instruction blank table) input (.write a i) ih
      (h*width (A := A)+i.val) (patched blank s h a.write i.val) out
      (some (.back a ⟨width (A := A)-1,by omega⟩)) (code blank a.write i) .stay .stay none
      (by simp only [instruction,hl,↓reduceDIte]; rfl)
      (by simpa only [Move.apply] using hi)
    simp only [Move.apply,patched_update,Option.toList_none,List.append_nil] at hs
    rw [show i.val+1=width (A := A) by have := i.isLt; omega,patched_full] at hs
    rw [show width (A := A)-i.val=1 by have := i.isLt; omega]
    simpa only [runFrom,Option.bind_some,hilast] using hs
termination_by width (A := A)-i.val
 decreasing_by have := i.isLt; omega

end EdgeSublinearMWIS.Main.CellBitCode
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.CellBitCode
open FiniteBitControl BitRoutine
variable {Q A : Type} [Fintype A] (blank : A)

 theorem move_run (table : CellControl.Table Q A) (input : List Bool)
    (next : Option Q) (direction : Move) (ih wh : ℕ) (w : ℕ → Bool) (out : List Bool)
    (hi : ih ≤ input.length+1) (m : ℕ) (hm : m ≤ width (A := A)) :
    runFrom (instruction blank table) input
      (cfg (some (.move next direction ⟨m,by omega⟩)) ih wh w out) (m+1) =
    some (cfg (next.map .ready) ih ((direction.apply^[m]) wh) w out) := by
  induction m generalizing wh with
  | zero =>
    have hs := step_cfg (instruction blank table) input (.move next direction ⟨0,by omega⟩)
      ih wh w out (next.map .ready) (w wh) .stay .stay none
      (by simp only [instruction,↓reduceIte]; rfl)
      (by simpa only [Move.apply] using hi)
    simpa only [runFrom,Option.bind_some,Move.apply,preserve,Option.toList_none,List.append_nil,
      Function.iterate_zero, id_eq] using hs
  | succ m ih' =>
    have hs := step_cfg (instruction blank table) input (.move next direction ⟨m+1,by omega⟩)
      ih wh w out (some (.move next direction ⟨m,by omega⟩)) (w wh) .stay direction none
      (by simp only [instruction,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel]; rfl)
      (by simpa only [Move.apply] using hi)
    simp only [Move.apply,preserve,Option.toList_none,List.append_nil] at hs
    rw [runFrom_succ_first,hs,Option.bind_some]
    simpa only [Function.iterate_succ_apply,Move.apply] using ih' (direction.apply wh) (by omega)

 theorem move_block (direction : Move) (h B : ℕ) : (direction.apply^[B]) (h*B) = direction.apply h * B := by
  cases direction with
  | stay =>
    have he : Move.stay.apply = id := rfl
    rw [he]; simp
  | right =>
    have he : Move.right.apply = Nat.succ := rfl
    rw [he,Nat.succ_iterate]
    simp [Nat.succ_mul,Nat.add_comm]
  | left =>
    have hx (n x : ℕ) : (Move.left.apply^[n]) x = x-n := by
      induction n generalizing x with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply,ih]; simp [Move.apply,Nat.sub_sub,Nat.add_comm]
    rw [hx,Move.apply,Nat.sub_mul]
    simp

end EdgeSublinearMWIS.Main.CellBitCode
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.CellBitCode
open FiniteBitControl BitRoutine
variable {Q A : Type} [Fintype A] (blank : A)

 def embed (c : CellControl.Configuration Q A) : FiniteBitControl.Configuration (State Q A) :=
  cfg (c.state.map .ready) c.inputHead (c.workHead * width (A := A)) (tape blank c.work) c.output

 theorem stride_origin (h : ℕ) : (h * width (A := A) == 0) = (h == 0) := by
  have hw : 0 < width (A := A) := by dsimp [width]; omega
  simp [Nat.mul_eq_zero, Nat.ne_of_gt hw]

 theorem step_run (table : CellControl.Table Q A) (input : List Bool)
    (c d : CellControl.Configuration Q A)
    (hi : c.inputHead ≤ input.length+1) (hs : CellControl.step table input c = some d) :
    runFrom (instruction blank table) input (embed blank c) (5 * width (A := A)+3) =
      some (embed blank d) := by
  rcases c with ⟨state,ih,h,s,out⟩
  cases state with
  | none =>
    have hd : d = ⟨none,ih,h,s,out⟩ := by simpa only [CellControl.step,Option.some.injEq] using hs.symm
    subst d
    exact runFrom_halt _ _ _ rfl _
  | some q =>
    let a := table q (if ih=0 then none else input[ih-1]?) (s h) (ih==0) (h==0)
    change (if a.inputMove.apply ih ≤ input.length+1 then
      some (⟨a.next,a.inputMove.apply ih,a.workMove.apply h,Function.update s h a.write,out ++ a.emit.toList⟩ : CellControl.Configuration Q A)
      else none) = some d at hs
    have ha : a.inputMove.apply ih ≤ input.length+1 := by
      by_contra hn
      simp only [hn,↓reduceIte,reduceCtorEq] at hs
    rw [if_pos ha] at hs
    have hd := (Option.some.inj hs).symm
    subst d
    have h0 := step_cfg (instruction blank table) input (.ready q) ih (h*width (A := A))
      (tape blank s) out
      (some (.read q (h==0) ⟨0,by dsimp [width]; omega⟩ (fun _ => false)))
      (tape blank s (h*width (A := A))) .stay .stay none
      (by simp only [instruction,stride_origin]; rfl)
      (by simpa only [Move.apply] using hi)
    simp only [Move.apply,preserve,Option.toList_none,List.append_nil] at h0
    have r0 : runFrom (instruction blank table) input (embed blank ⟨some q,ih,h,s,out⟩) 1 =
      some (cfg (some (.read q (h==0) ⟨0,by dsimp [width]; omega⟩ (fun _ => false))) ih
        (h*width (A := A)) (tape blank s) out) := h0
    have r1 := read_run blank table input q (h==0) ih h s out hi ⟨0,by dsimp [width]; omega⟩
    simp only [readPrefix,Nat.not_lt_zero,↓reduceIte,Nat.add_zero,Nat.sub_zero] at r1
    have r2 := rewind_run blank table input a ih (h*width (A := A)) (tape blank s) out hi
      (width (A := A)-1) (by omega)
    have r3 := write_run blank table input a ih h s out hi ⟨0,by dsimp [width]; omega⟩
    simp only [patched_zero,Nat.add_zero,Nat.sub_zero] at r3
    have r4 := back_run blank table input a ih (h*width (A := A))
      (tape blank (Function.update s h a.write)) out hi (width (A := A)-1) (by omega)
    have h5 := step_cfg (instruction blank table) input (.commit a) ih (h*width (A := A))
      (tape blank (Function.update s h a.write)) out
      (some (.move a.next a.workMove ⟨width (A := A),by omega⟩))
      (tape blank (Function.update s h a.write) (h*width (A := A))) a.inputMove .stay a.emit rfl ha
    simp only [Move.apply,preserve] at h5
    have r5 : runFrom (instruction blank table) input
      (cfg (some (.commit a)) ih (h*width (A := A)) (tape blank (Function.update s h a.write)) out) 1 = _ := h5
    have r6 := move_run blank table input a.next a.workMove (a.inputMove.apply ih) (h*width (A := A))
      (tape blank (Function.update s h a.write)) (out ++ a.emit.toList) ha (width (A := A)) (by omega)
    have rwid : width (A := A)-1+1=width (A := A) := by simp [width]
    rw [rwid] at r2 r4
    have hh := runFrom_trans _ _ _ _ _ _ _ r0 r1
    have hh := runFrom_trans _ _ _ _ _ _ _ hh r2
    have hh := runFrom_trans _ _ _ _ _ _ _ hh r3
    have hh := runFrom_trans _ _ _ _ _ _ _ hh r4
    have hh := runFrom_trans _ _ _ _ _ _ _ hh r5
    have hh := runFrom_trans _ _ _ _ _ _ _ hh r6
    rw [move_block] at hh
    convert hh using 1 <;> dsimp only [embed] <;> congr 1 <;> omega

 theorem run_pair (table : CellControl.Table Q A) (input : List Bool)
    (c : CellControl.Configuration Q A) (hi : c.inputHead ≤ input.length+1)
    (t : ℕ) (d : CellControl.Configuration Q A)
    (hr : CellControl.runFrom table input c t = some d) :
    d.inputHead ≤ input.length+1 ∧
    runFrom (instruction blank table) input (embed blank c) ((5*width (A := A)+3)*t) = some (embed blank d) := by
  induction t generalizing d with
  | zero =>
    have hd := Option.some.inj hr
    subst d
    exact ⟨hi,rfl⟩
  | succ t ih' =>
    cases he : CellControl.runFrom table input c t with
    | none => simp only [CellControl.runFrom,he,Option.bind_none,reduceCtorEq] at hr
    | some e =>
      have hs : CellControl.step table input e = some d := by
        simpa only [CellControl.runFrom,he,Option.bind_some] using hr
      have hp := ih' e he
      refine ⟨CellControl.step_input_bound table input e d hp.1 hs,?_⟩
      rw [Nat.mul_succ]
      exact runFrom_trans _ _ _ _ _ _ _ hp.2 (step_run blank table input e d hp.1 hs)

end EdgeSublinearMWIS.Main.CellBitCode
end

noncomputable section

open CatalyticMatching.General EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BitExecutionHelpers

 theorem run_after_halt (M : Machine) (input catalyst : List Bool) (t : ℕ) (c : Configuration M)
    (hrun : M.run input catalyst t = some c) (hstate : c.state = none) (s : ℕ) :
    M.run input catalyst (t + s) = some c := by
  induction s with
  | zero => simpa using hrun
  | succ s ih =>
    rw [Nat.add_succ, Machine.run, ih]
    simp only [Option.bind_some, Machine.step, hstate]

 theorem first_halt (M : Machine) (input output : List Bool) (T : ℕ) (c : Configuration M)
    (hrun : M.run input [] T = some c) (hstate : c.state = none) (hout : c.output = output) :
    ∃ s ≤ T, BitHalts M input output s := by
  classical
  let H : ℕ → Prop := fun t => ∃ c : Configuration M, M.run input [] t = some c ∧ c.state = none
  have hex : ∃ t, H t := ⟨T,c,hrun,hstate⟩
  let s := Nat.find hex
  have hsT : s ≤ T := Nat.find_min' hex ⟨c,hrun,hstate⟩
  obtain ⟨c0, hc0, hstate0⟩ := Nat.find_spec hex
  have hfinal := run_after_halt M input [] s c0 hc0 hstate0 (T - s)
  rw [show s + (T - s) = T from Nat.add_sub_of_le hsT] at hfinal
  have heq : c0 = c := Option.some.inj (hfinal.symm.trans hrun)
  refine ⟨s, hsT, c0, hc0, hstate0, heq ▸ hout, ?_⟩
  intro j hj c' hc' hnone
  exact Nat.find_min hex hj ⟨c',hc',hnone⟩

end EdgeSublinearMWIS.Main.BitExecutionHelpers
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.CellBitCode
open FiniteBitControl BitRoutine
variable {Q A : Type} [Fintype Q] [Fintype A] (blank : A)

 def compile (start : Q) (table : CellControl.Table Q A) : Machine :=
  machine (.ready start) (instruction blank table)

 theorem compile_halts (start : Q) (table : CellControl.Table Q A) (input output : List Bool)
    (t : ℕ) (d : CellControl.Configuration Q A)
    (hr : CellControl.runFrom table input ⟨some start,0,0,fun _ => blank,[]⟩ t = some d)
    (hd : d.state = none) (ho : d.output = output) :
    ∃ s ≤ (5*width (A := A)+3)*t, BitHalts (compile blank start table) input output s := by
  have hp := (run_pair blank table input ⟨some start,0,0,fun _ => blank,[]⟩ (by simp) t d hr).2
  have he : embed blank (⟨some start,0,0,fun _ => blank,[]⟩ : CellControl.Configuration Q A) =
      initial (.ready start) [] := by
    simp only [embed,cfg,tape_blank,Option.map_some,Nat.zero_mul,initial]
  rw [he,runFrom_initial] at hp
  have hh := congrArg (Option.map (encode (.ready start) (instruction blank table))) hp
  rw [run_encode,Option.map_some] at hh
  apply BitExecutionHelpers.first_halt (compile blank start table) input output _ _ hh
  · change (d.state.map State.ready).map (Fintype.equivFin (State Q A)) = none
    rw [hd]; rfl
  · exact ho

end EdgeSublinearMWIS.Main.CellBitCode
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

abbrev Cell (P : Program) := ∀ k, Option (P.machine.tm.Γ k)

def blank (P : Program) : Cell P := fun _ => none

def cells (P : Program) (S : ∀ k, List (P.machine.tm.Γ k)) (j : ℕ) : Cell P := fun k => (S k)[j]?

 theorem child_mem (P : Program) (q : Statement P) (q' : P.machine.tm.Stmt)
    (h : q' ∈ Turing.TM2.stmts₁ q.val) : q' ∈ allStatements P := by
  rcases Finset.mem_biUnion.mp q.property with ⟨l,hl,hq⟩
  exact Finset.mem_biUnion.mpr ⟨l,hl,Turing.TM2.stmts₁_trans hq h⟩

 def child (P : Program) (q : Statement P) (q' : P.machine.tm.Stmt)
    (h : q' ∈ Turing.TM2.stmts₁ q.val) : Statement P := ⟨q',child_mem P q q' h⟩

 def mainResume (P : Program) (l : P.machine.tm.Λ) (v : P.machine.tm.σ) : Resume P :=
  (⟨P.machine.tm.m l,main_mem P l⟩,v)

inductive CellState (P : Program) where
  | initStart
  | initLoop
  | returnTo (r : Resume P)
  | exec (r : Resume P)
  | push (k : P.machine.tm.K) (carry : P.machine.tm.Γ k) (r : Resume P)
  | popNext (k : P.machine.tm.K) (r : Resume P)
  | popWrite (k : P.machine.tm.K) (carry : Option (P.machine.tm.Γ k)) (r : Resume P)
  | popAdvance (k : P.machine.tm.K) (r : Resume P)
  | output
  deriving Fintype

 def cellInstruction (P : Program) : CellControl.Table (CellState P) (Cell P) := fun state inp cell _ wo =>
  match state with
  | .initStart => ⟨some .initLoop,cell,.right,.stay,none⟩
  | .initLoop =>
    match inp with
    | some b => ⟨some .initLoop,Function.update cell P.machine.tm.k₀ (some (P.machine.inputAlphabet.symm b)),.right,.right,none⟩
    | none => ⟨some (.returnTo (mainResume P P.machine.tm.main P.machine.tm.initialState)),cell,.stay,.stay,none⟩
  | .returnTo r =>
    if wo then ⟨some (.exec r),cell,.stay,.stay,none⟩
    else ⟨some (.returnTo r),cell,.stay,.left,none⟩
  | .exec r =>
    match hq : r.1.val with
    | .push k f q =>
      ⟨some (.push k (f r.2) (child P r.1 q (by rw [hq]; exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self),r.2)),cell,.stay,.stay,none⟩
    | .peek k f q =>
      ⟨some (.exec (child P r.1 q (by rw [hq]; exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self),f r.2 (cell k))),cell,.stay,.stay,none⟩
    | .pop k f q =>
      ⟨some (.popNext k (child P r.1 q (by rw [hq]; exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self),f r.2 (cell k))),cell,.stay,.right,none⟩
    | .load f q =>
      ⟨some (.exec (child P r.1 q (by rw [hq]; exact Finset.mem_insert_of_mem Turing.TM2.stmts₁_self),f r.2)),cell,.stay,.stay,none⟩
    | .branch f q u =>
      if f r.2 then
        ⟨some (.exec (child P r.1 q (by rw [hq]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ Turing.TM2.stmts₁_self)),r.2)),cell,.stay,.stay,none⟩
      else
        ⟨some (.exec (child P r.1 u (by rw [hq]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ Turing.TM2.stmts₁_self)),r.2)),cell,.stay,.stay,none⟩
    | .goto f => ⟨some (.exec (mainResume P (f r.2) r.2)),cell,.stay,.stay,none⟩
    | .halt => ⟨some .output,cell,.stay,.stay,none⟩
  | .push k carry r =>
    ⟨some (match cell k with | some old => .push k old r | none => .returnTo r),
      Function.update cell k (some carry),.stay,(if (cell k).isSome then .right else .stay),none⟩
  | .popNext k r => ⟨some (.popWrite k (cell k) r),cell,.stay,.left,none⟩
  | .popWrite k carry r =>
    ⟨some (match carry with | some _ => .popAdvance k r | none => .returnTo r),
      Function.update cell k carry,.stay,(if carry.isSome then .right else .stay),none⟩
  | .popAdvance k r => ⟨some (.popNext k r),cell,.stay,.right,none⟩
  | .output =>
    match cell P.machine.tm.k₁ with
    | none => ⟨none,cell,.stay,.stay,none⟩
    | some b => ⟨some .output,cell,.stay,.right,some (P.machine.outputAlphabet b)⟩

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.CellRoutine
open CellControl
variable {Q A : Type}

def cfg (state : Option Q) (ih wh : ℕ) (w : ℕ → A) (out : List Bool) : Configuration Q A :=
  ⟨state,ih,wh,w,out⟩

theorem step_cfg (table : Table Q A) (input : List Bool) (q : Q) (ih wh : ℕ) (w : ℕ → A)
    (out : List Bool) (a : Instruction Q A)
    (ht : table q (if ih=0 then none else input[ih-1]?) (w wh) (ih==0) (wh==0) = a)
    (hi : a.inputMove.apply ih ≤ input.length+1) :
    step table input (cfg (some q) ih wh w out) =
      some (cfg a.next (a.inputMove.apply ih) (a.workMove.apply wh)
        (Function.update w wh a.write) (out ++ a.emit.toList)) := by
  dsimp only [step,cfg]
  rw [ht,if_pos hi]

 theorem runFrom_succ_first (table : Table Q A) (input : List Bool) (c : Configuration Q A) (t : ℕ) :
    runFrom table input c (t+1) = (step table input c).bind (fun d => runFrom table input d t) := by
  rw [show t+1=1+t by omega,runFrom_add]
  rfl

end EdgeSublinearMWIS.Main.CellRoutine
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin
open CellControl CellRoutine

 theorem return_run (P : Program) (input : List Bool) (r : Resume P)
    (ih h : ℕ) (w : ℕ → Cell P) (out : List Bool) (hi : ih ≤ input.length+1) :
    runFrom (cellInstruction P) input (cfg (some (.returnTo r)) ih h w out) (h+1) =
      some (cfg (some (.exec r)) ih 0 w out) := by
  induction h with
  | zero =>
    have hs := step_cfg (cellInstruction P) input (.returnTo r) ih 0 w out
      ⟨some (.exec r),w 0,.stay,.stay,none⟩
      (by simp only [cellInstruction,beq_self_eq_true,↓reduceIte]) hi
    simpa only [runFrom,Option.bind_some,Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil] using hs
  | succ h ih' =>
    have hs := step_cfg (cellInstruction P) input (.returnTo r) ih (h+1) w out
      ⟨some (.returnTo r),w (h+1),.stay,.left,none⟩
      (by simp only [cellInstruction,beq_iff_eq,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte]) hi
    simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil,Nat.add_sub_cancel] at hs
    rw [runFrom_succ_first,hs,Option.bind_some]
    exact ih'

 theorem output_run (P : Program) (input : List Bool) (ih j : ℕ) (w : ℕ → Cell P)
    (out : List Bool) (L : List (P.machine.tm.Γ P.machine.tm.k₁))
    (hi : ih ≤ input.length+1) (hw : ∀ i, w (j+i) P.machine.tm.k₁ = L[i]?) :
    runFrom (cellInstruction P) input (cfg (some .output) ih j w out) (L.length+1) =
      some (cfg none ih (j+L.length) w (out ++ L.map P.machine.outputAlphabet)) := by
  induction L generalizing j out with
  | nil =>
    have hhead : w j P.machine.tm.k₁=none := by simpa only [Nat.add_zero,List.getElem?_nil] using hw 0
    have hs := step_cfg (cellInstruction P) input .output ih j w out
      ⟨none,w j,.stay,.stay,none⟩
      (by simp only [cellInstruction,hhead]) hi
    simpa only [runFrom,Option.bind_some,Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil,
      List.length_nil,List.map_nil,Nat.add_zero] using hs
  | cons a L ih' =>
    have hhead : w j P.machine.tm.k₁=some a := by simpa only [Nat.add_zero,List.getElem?_cons_zero] using hw 0
    have hs := step_cfg (cellInstruction P) input .output ih j w out
      ⟨some .output,w j,.stay,.right,some (P.machine.outputAlphabet a)⟩
      (by simp only [cellInstruction,hhead]) hi
    simp only [Move.apply,Function.update_eq_self,Option.toList_some] at hs
    rw [List.length_cons,runFrom_succ_first,hs,Option.bind_some]
    have ht : ∀ i, w (j+1+i) P.machine.tm.k₁=L[i]? := by
      intro i
      simpa only [Nat.add_assoc,Nat.add_comm 1 i,List.getElem?_cons_succ] using hw (i+1)
    simpa only [List.map_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm 1 L.length] using ih' (j+1) (out ++ [P.machine.outputAlphabet a]) ht

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def paint (P : Program) (w : ℕ → Cell P) (k : P.machine.tm.K) (base : ℕ)
    (L : List (P.machine.tm.Γ k)) (p : ℕ) : Cell P :=
  if base ≤ p ∧ p-base<L.length then Function.update (w p) k L[p-base]? else w p

 theorem paint_nil (P : Program) (w : ℕ → Cell P) (k : P.machine.tm.K) (base : ℕ) :
    paint P w k base [] = w := by funext p; simp [paint]

 theorem paint_cons (P : Program) (w : ℕ → Cell P) (k : P.machine.tm.K) (base : ℕ)
    (a : P.machine.tm.Γ k) (L : List (P.machine.tm.Γ k)) :
    paint P (Function.update w base (Function.update (w base) k (some a))) k (base+1) L =
      paint P w k base (a::L) := by
  funext p
  by_cases hp : p=base
  · subst p
    simp [paint]
  · have he : Function.update w base (Function.update (w base) k (some a)) p=w p := Function.update_of_ne hp _ _
    by_cases hb : base ≤ p
    · have hb' : base+1 ≤ p := by omega
      have hm : p-base=(p-(base+1))+1 := by omega
      simp only [paint,he,hb,hb',true_and,List.length_cons,hm,Nat.add_lt_add_iff_right,
        List.getElem?_cons_succ]
    · have hb' : ¬base+1 ≤ p := by omega
      simp only [paint,he,hb,hb',false_and,↓reduceIte]

 theorem paint_singleton (P : Program) (w : ℕ → Cell P) (k : P.machine.tm.K) (base : ℕ)
    (a : P.machine.tm.Γ k) :
    paint P w k base [a] = Function.update w base (Function.update (w base) k (some a)) := by
  have hh := paint_cons P w k base a []
  rw [paint_nil] at hh
  exact hh.symm

 theorem paint_cells_push (P : Program) (S : ∀ k, List (P.machine.tm.Γ k)) (k : P.machine.tm.K)
    (a : P.machine.tm.Γ k) :
    paint P (cells P S) k 0 (a::S k) = cells P (Function.update S k (a::S k)) := by
  funext p j
  by_cases hj : j=k
  · subst j
    cases p with
    | zero => simp [paint,cells]
    | succ p =>
      by_cases hp : p < (S k).length
      · simp [paint,cells,hp]
      · have hl : (S k).length ≤ p := by omega
        have hl' : (S k).length ≤ p+1 := by omega
        simp [paint,cells,hp,List.getElem?_eq_none hl,List.getElem?_eq_none hl']
  · unfold paint
    split_ifs <;> simp [cells,Function.update_of_ne hj]

 theorem updated_track (P : Program) (w : ℕ → Cell P) (k : P.machine.tm.K)
    (base : ℕ) (a : P.machine.tm.Γ k) (L : List (P.machine.tm.Γ k))
    (hw : ∀ i, w (base+i) k=(a::L)[i]?) (b : Option (P.machine.tm.Γ k)) :
    ∀ i, Function.update w base (Function.update (w base) k b) (base+1+i) k=L[i]? := by
  intro i
  have hn : base+1+i≠base := by omega
  rw [Function.update_of_ne hn]
  simpa only [Nat.add_assoc,Nat.add_comm 1 i,List.getElem?_cons_succ] using hw (i+1)

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin
open CellControl CellRoutine

 theorem push_loop (P : Program) (input : List Bool) (k : P.machine.tm.K) (r : Resume P)
    (ih base : ℕ) (w : ℕ → Cell P) (out : List Bool) (carry : P.machine.tm.Γ k)
    (L : List (P.machine.tm.Γ k)) (hi : ih ≤ input.length+1)
    (hw : ∀ i, w (base+i) k=L[i]?) :
    runFrom (cellInstruction P) input (cfg (some (.push k carry r)) ih base w out) (L.length+1) =
      some (cfg (some (.returnTo r)) ih (base+L.length) (paint P w k base (carry::L)) out) := by
  induction L generalizing base w carry with
  | nil =>
    have hhead : w base k=none := by simpa only [Nat.add_zero,List.getElem?_nil] using hw 0
    have hs := step_cfg (cellInstruction P) input (.push k carry r) ih base w out
      ⟨some (.returnTo r),Function.update (w base) k (some carry),.stay,.stay,none⟩
      (by simp [cellInstruction,hhead]) hi
    simpa only [runFrom,Option.bind_some,Move.apply,Option.toList_none,List.append_nil,
      List.length_nil,Nat.add_zero,paint_singleton] using hs
  | cons a L ih' =>
    have hhead : w base k=some a := by simpa only [Nat.add_zero,List.getElem?_cons_zero] using hw 0
    let w' := Function.update w base (Function.update (w base) k (some carry))
    have hs := step_cfg (cellInstruction P) input (.push k carry r) ih base w out
      ⟨some (.push k a r),Function.update (w base) k (some carry),.stay,.right,none⟩
      (by simp [cellInstruction,hhead]) hi
    simp only [Move.apply,Option.toList_none,List.append_nil] at hs
    rw [List.length_cons,runFrom_succ_first,hs,Option.bind_some]
    have ht : ∀ i, w' (base+1+i) k=L[i]? := updated_track P w k base a L hw (some carry)
    have hh := ih' (base+1) w' a ht
    simpa only [w',paint_cons,Nat.add_assoc,Nat.add_comm 1 L.length] using hh

 theorem push_run (P : Program) (input : List Bool) (k : P.machine.tm.K) (r : Resume P)
    (ih : ℕ) (S : ∀ k, List (P.machine.tm.Γ k)) (out : List Bool) (a : P.machine.tm.Γ k)
    (hi : ih ≤ input.length+1) :
    runFrom (cellInstruction P) input (cfg (some (.push k a r)) ih 0 (cells P S) out)
      (2*(S k).length+2) =
      some (cfg (some (.exec r)) ih 0 (cells P (Function.update S k (a::S k))) out) := by
  have h1 := push_loop P input k r ih 0 (cells P S) out a (S k) hi (by intro i; simp only [cells,Nat.zero_add])
  have h2 := return_run P input r ih (0+(S k).length) (paint P (cells P S) k 0 (a::S k)) out hi
  have hh := runFrom_trans _ _ _ _ _ _ _ h1 h2
  rw [paint_cells_push] at hh
  rw [show (S k).length+1+(0+(S k).length+1)=2*(S k).length+2 by omega] at hh
  exact hh

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def popPaint (P : Program) (w : ℕ → Cell P) (k : P.machine.tm.K) (base : ℕ)
    (L : List (P.machine.tm.Γ k)) (p : ℕ) : Cell P :=
  if base ≤ p ∧ p-base≤L.length then Function.update (w p) k L[p-base]? else w p

 theorem popPaint_nil (P : Program) (w : ℕ → Cell P) (k : P.machine.tm.K) (base : ℕ) :
    popPaint P w k base [] = Function.update w base (Function.update (w base) k none) := by
  funext p
  by_cases hp : p=base
  · subst p; simp [popPaint]
  · have h : ¬(base≤p ∧ p-base≤0) := by omega
    unfold popPaint
    simp only [List.length_nil]
    rw [if_neg h,Function.update_of_ne hp]

 theorem popPaint_cons (P : Program) (w : ℕ → Cell P) (k : P.machine.tm.K) (base : ℕ)
    (a : P.machine.tm.Γ k) (L : List (P.machine.tm.Γ k)) :
    popPaint P (Function.update w base (Function.update (w base) k (some a))) k (base+1) L =
      popPaint P w k base (a::L) := by
  funext p
  by_cases hp : p=base
  · subst p; simp [popPaint]
  · have he : Function.update w base (Function.update (w base) k (some a)) p=w p := Function.update_of_ne hp _ _
    by_cases hb : base≤p
    · have hb' : base+1≤p := by omega
      have hm : p-base=(p-(base+1))+1 := by omega
      simp only [popPaint,he,hb,hb',true_and,List.length_cons,hm,Nat.add_le_add_iff_right,List.getElem?_cons_succ]
    · have hb' : ¬base+1≤p := by omega
      simp only [popPaint,he,hb,hb',false_and,↓reduceIte]

 theorem popPaint_cells (P : Program) (S : ∀ k, List (P.machine.tm.Γ k)) (k : P.machine.tm.K) :
    popPaint P (cells P S) k 0 (S k).tail = cells P (Function.update S k (S k).tail) := by
  funext p j
  by_cases hj : j=k
  · subst j
    by_cases hp : p≤(S k).tail.length
    · unfold popPaint
      rw [if_pos ⟨Nat.zero_le p,by simpa only [Nat.sub_zero] using hp⟩]
      simp [cells]
    · have hl : (S k).tail.length≤p := by omega
      have hl' : (S k).length≤p := by simp only [List.length_tail] at hp; omega
      unfold popPaint
      rw [if_neg (show ¬(0≤p ∧ p-0≤(S k).tail.length) by omega)]
      simp [cells,List.getElem?_eq_none hl,List.getElem?_eq_none hl']
  · unfold popPaint
    split_ifs <;> simp [cells,Function.update_of_ne hj]

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin
open CellControl CellRoutine

 theorem pop_loop (P : Program) (input : List Bool) (k : P.machine.tm.K) (r : Resume P)
    (ih base : ℕ) (w : ℕ → Cell P) (out : List Bool) (L : List (P.machine.tm.Γ k))
    (hi : ih ≤ input.length+1) (hw : ∀ i, w (base+1+i) k=L[i]?) :
    runFrom (cellInstruction P) input (cfg (some (.popNext k r)) ih (base+1) w out) (3*L.length+2) =
      some (cfg (some (.returnTo r)) ih (base+L.length) (popPaint P w k base L) out) := by
  induction L generalizing base w with
  | nil =>
    have hhead : w (base+1) k=none := by simpa only [Nat.add_zero,List.getElem?_nil] using hw 0
    have hs1 := step_cfg (cellInstruction P) input (.popNext k r) ih (base+1) w out
      ⟨some (.popWrite k none r),w (base+1),.stay,.left,none⟩
      (by simp only [cellInstruction,hhead]) hi
    simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil,Nat.add_sub_cancel] at hs1
    have hs2 := step_cfg (cellInstruction P) input (.popWrite k none r) ih base w out
      ⟨some (.returnTo r),Function.update (w base) k none,.stay,.stay,none⟩
      (by simp [cellInstruction]) hi
    simp only [Move.apply,Option.toList_none,List.append_nil] at hs2
    rw [show 3*List.length ([] : List (P.machine.tm.Γ k))+2=1+1 by rfl,runFrom_succ_first,hs1,Option.bind_some]
    simpa only [runFrom,Option.bind_some,List.length_nil,Nat.add_zero,popPaint_nil] using hs2
  | cons a L ih' =>
    have hhead : w (base+1) k=some a := by simpa only [Nat.add_zero,List.getElem?_cons_zero] using hw 0
    let w' := Function.update w base (Function.update (w base) k (some a))
    have hs1 := step_cfg (cellInstruction P) input (.popNext k r) ih (base+1) w out
      ⟨some (.popWrite k (some a) r),w (base+1),.stay,.left,none⟩
      (by simp only [cellInstruction,hhead]) hi
    simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil,Nat.add_sub_cancel] at hs1
    have hs2 := step_cfg (cellInstruction P) input (.popWrite k (some a) r) ih base w out
      ⟨some (.popAdvance k r),Function.update (w base) k (some a),.stay,.right,none⟩
      (by simp [cellInstruction]) hi
    simp only [Move.apply,Option.toList_none,List.append_nil] at hs2
    have hs3 := step_cfg (cellInstruction P) input (.popAdvance k r) ih (base+1) w' out
      ⟨some (.popNext k r),w' (base+1),.stay,.right,none⟩ rfl hi
    simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil] at hs3
    rw [show 3*(a::L).length+2=((3*L.length+2)+1)+1+1 by simp only [List.length_cons]; omega,
      runFrom_succ_first,hs1,Option.bind_some,runFrom_succ_first,hs2,Option.bind_some,
      runFrom_succ_first,hs3,Option.bind_some]
    have ht : ∀ i, w' (base+1+1+i) k=L[i]? := by
      intro i
      rw [show w' (base+1+1+i)=w (base+1+1+i) from Function.update_of_ne (by omega) _ _]
      simpa only [Nat.add_assoc,Nat.add_comm 1 i,List.getElem?_cons_succ] using hw (i+1)
    simpa only [List.length_cons,w',popPaint_cons,Nat.add_assoc,Nat.add_comm 1 L.length] using ih' (base+1) w' ht

 theorem pop_run (P : Program) (input : List Bool) (k : P.machine.tm.K) (r : Resume P)
    (ih : ℕ) (S : ∀ k, List (P.machine.tm.Γ k)) (out : List Bool) (hi : ih ≤ input.length+1) :
    runFrom (cellInstruction P) input (cfg (some (.popNext k r)) ih 1 (cells P S) out)
      (4*(S k).tail.length+3) =
      some (cfg (some (.exec r)) ih 0 (cells P (Function.update S k (S k).tail)) out) := by
  have h1 := pop_loop P input k r ih 0 (cells P S) out (S k).tail hi
    (by intro i; simp only [cells,Nat.zero_add,List.getElem?_tail,Nat.add_comm 1 i])
  have h2 := return_run P input r ih (0+(S k).tail.length)
    (popPaint P (cells P S) k 0 (S k).tail) out hi
  have hh := runFrom_trans _ _ _ _ _ _ _ h1 h2
  rw [popPaint_cells,show 3*(S k).tail.length+2+(0+(S k).tail.length+1)=4*(S k).tail.length+3 by omega] at hh
  exact hh

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin
open CellControl CellRoutine

 def initTape (P : Program) (input : List Bool) (m j : ℕ) : Cell P :=
  Function.update (blank P) P.machine.tm.k₀
    (if j < m then input[j]?.map P.machine.inputAlphabet.symm else none)

 theorem initTape_zero (P : Program) (input : List Bool) : initTape P input 0 = fun _ => blank P := by
  funext j k
  by_cases hk : k=P.machine.tm.k₀
  · subst k; simp [initTape,blank]
  · simp [initTape,blank,Function.update_of_ne hk]

 theorem initTape_end (P : Program) (input : List Bool) : initTape P input input.length =
    cells P (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)).stk := by
  funext j k
  by_cases hk : k=P.machine.tm.k₀
  · subst k
    by_cases hj : j < input.length
    · simp [initTape,cells,Turing.initList,hj]
    · have hl : input.length ≤ j := by omega
      simp [initTape,cells,Turing.initList,hj,List.getElem?_eq_none hl]
  · simp [initTape,cells,Turing.initList,blank,Function.update_of_ne hk,hk]

 theorem initTape_advance (P : Program) (input : List Bool) (m : ℕ) (b : Bool)
    (hb : input[m]?=some b) :
    Function.update (initTape P input m) m
      (Function.update (initTape P input m m) P.machine.tm.k₀ (some (P.machine.inputAlphabet.symm b))) =
    initTape P input (m+1) := by
  funext j
  by_cases hj : j=m
  · subst j
    simp [initTape,hb,Function.update_idem]
  · have hh : (j < m+1) ↔ j < m := by omega
    simp only [Function.update_of_ne hj,initTape,hh]

 theorem init_loop (P : Program) (input : List Bool) (j : ℕ) (hj : j ≤ input.length) :
    runFrom (cellInstruction P) input (cfg (some .initLoop) (j+1) j (initTape P input j) []) (input.length-j+1) =
      some (cfg (some (.returnTo (mainResume P P.machine.tm.main P.machine.tm.initialState)))
        (input.length+1) input.length
        (cells P (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)).stk) []) := by
  by_cases hl : j < input.length
  · let b := input[j]
    have hb : input[j]?=some b := List.getElem?_eq_getElem hl
    have hs := step_cfg (cellInstruction P) input .initLoop (j+1) j (initTape P input j) []
      ⟨some .initLoop,Function.update (initTape P input j j) P.machine.tm.k₀ (some (P.machine.inputAlphabet.symm b)),.right,.right,none⟩
      (by simp [cellInstruction,hb]) (by dsimp [Move.apply]; omega)
    simp only [Move.apply,initTape_advance P input j b hb,Option.toList_none,List.append_nil] at hs
    rw [show input.length-j+1=(input.length-(j+1)+1)+1 by omega,
      runFrom_succ_first,hs,Option.bind_some]
    exact init_loop P input (j+1) (by omega)
  · have he : j=input.length := by omega
    subst j
    have hs := step_cfg (cellInstruction P) input .initLoop (input.length+1) input.length (initTape P input input.length) []
      ⟨some (.returnTo (mainResume P P.machine.tm.main P.machine.tm.initialState)),initTape P input input.length input.length,.stay,.stay,none⟩
      (by simp [cellInstruction]) (by dsimp [Move.apply]; omega)
    simpa only [Nat.sub_self,Nat.zero_add,runFrom,Option.bind_some,Move.apply,Function.update_eq_self,
      Option.toList_none,List.append_nil,initTape_end] using hs
termination_by input.length-j
 decreasing_by omega

 theorem initialize_run (P : Program) (input : List Bool) :
    runFrom (cellInstruction P) input (cfg (some .initStart) 0 0 (fun _ => blank P) []) (2*input.length+3) =
      some (cfg (some (.exec (mainResume P P.machine.tm.main P.machine.tm.initialState)))
        (input.length+1) 0 (cells P (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)).stk) []) := by
  have hs := step_cfg (cellInstruction P) input .initStart 0 0 (fun _ => blank P) []
    ⟨some .initLoop,blank P,.right,.stay,none⟩ rfl (by simp [Move.apply])
  simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil] at hs
  have h0 : runFrom (cellInstruction P) input (cfg (some .initStart) 0 0 (fun _ => blank P) []) 1 = _ := hs
  have h1 := init_loop P input 0 (Nat.zero_le _)
  rw [initTape_zero] at h1
  simp only [Nat.zero_add,Nat.sub_zero] at h1
  have h2 := return_run P input (mainResume P P.machine.tm.main P.machine.tm.initialState)
    (input.length+1) input.length (cells P (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)).stk) [] (by omega)
  have hh := runFrom_trans _ _ _ _ _ _ _ h0 h1
  have hh := runFrom_trans _ _ _ _ _ _ _ hh h2
  rw [show 1+(input.length+1)+(input.length+1)=2*input.length+3 by omega] at hh
  exact hh

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin
open CellControl CellRoutine StackSpace

 def endpoint (P : Program) (c : P.machine.tm.Cfg) (ih : ℕ) : CellControl.Configuration (CellState P) (Cell P) :=
  cfg (some (match c.l with | none => .output | some l => .exec (mainResume P l c.var))) ih 0 (cells P c.stk) []

 theorem exec_run (P : Program) (input : List Bool) (ih : ℕ) (hi : ih ≤ input.length+1)
    (q : Turing.TM2.Stmt P.machine.tm.Γ P.machine.tm.Λ P.machine.tm.σ)
    (hq : q ∈ allStatements P) (v : P.machine.tm.σ) (S : ∀ k, List (P.machine.tm.Γ k)) :
    ∃ t, t ≤ 8*cost q*(space S+cost q+1) ∧
      runFrom (cellInstruction P) input (cfg (some (.exec (⟨q,hq⟩,v))) ih 0 (cells P S) []) t =
        some (endpoint P (Turing.TM2.stepAux q v S) ih) := by
  induction q generalizing v S with
  | push k f q ih' =>
    let r : Resume P := (child P ⟨.push k f q,hq⟩ q (Finset.mem_insert_of_mem Turing.TM2.stmts₁_self),v)
    let S' := Function.update S k (f v::S k)
    obtain ⟨t,ht,hr⟩ := ih' r.1.property v S'
    have hs := step_cfg (cellInstruction P) input (.exec (⟨.push k f q,hq⟩,v)) ih 0 (cells P S) []
      ⟨some (.push k (f v) r),cells P S 0,.stay,.stay,none⟩ rfl hi
    simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil] at hs
    have h0 : runFrom (cellInstruction P) input (cfg (some (.exec (⟨.push k f q,hq⟩,v))) ih 0 (cells P S) []) 1 = _ := hs
    have h1 := push_run P input k r ih S [] (f v) hi
    have hh := runFrom_trans _ _ _ _ _ _ _ h0 h1
    have hh := runFrom_trans _ _ _ _ _ _ _ hh hr
    refine ⟨1+(2*(S k).length+2)+t,?_,hh⟩
    have hl := stack_length_le_space S k
    have he : space S'=space S+1 := by
      have hu := space_update S k (f v::S k)
      simp only [List.length_cons] at hu
      dsimp [S']; omega
    rw [he] at ht
    simp only [cost]
    nlinarith [cost_pos q]
  | pop k f q ih' =>
    let r : Resume P := (child P ⟨.pop k f q,hq⟩ q (Finset.mem_insert_of_mem Turing.TM2.stmts₁_self),f v (S k).head?)
    let S' := Function.update S k (S k).tail
    obtain ⟨t,ht,hr⟩ := ih' r.1.property r.2 S'
    have hs := step_cfg (cellInstruction P) input (.exec (⟨.pop k f q,hq⟩,v)) ih 0 (cells P S) []
      ⟨some (.popNext k r),cells P S 0,.stay,.right,none⟩ (by simp only [cellInstruction,r,child,cells,List.head?_eq_getElem?]) hi
    simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil] at hs
    have h0 : runFrom (cellInstruction P) input (cfg (some (.exec (⟨.pop k f q,hq⟩,v))) ih 0 (cells P S) []) 1 = _ := hs
    have h1 := pop_run P input k r ih S [] hi
    have hh := runFrom_trans _ _ _ _ _ _ _ h0 h1
    have hh := runFrom_trans _ _ _ _ _ _ _ hh hr
    refine ⟨1+(4*(S k).tail.length+3)+t,?_,hh⟩
    have hl := stack_length_le_space S k
    have htail : (S k).tail.length ≤ (S k).length := by simp only [List.length_tail]; omega
    have he : space S' ≤ space S := by
      have hu := space_update S k (S k).tail
      dsimp [S']; omega
    have ht' : t ≤ 8*cost q*(space S+cost q+1) := ht.trans (Nat.mul_le_mul_left _ (by omega))
    simp only [cost]
    nlinarith [cost_pos q]
  | peek k f q ih' =>
    let r : Resume P := (child P ⟨.peek k f q,hq⟩ q (Finset.mem_insert_of_mem Turing.TM2.stmts₁_self),f v (S k).head?)
    obtain ⟨t,ht,hr⟩ := ih' r.1.property r.2 S
    have hs := step_cfg (cellInstruction P) input (.exec (⟨.peek k f q,hq⟩,v)) ih 0 (cells P S) []
      ⟨some (.exec r),cells P S 0,.stay,.stay,none⟩ (by simp only [cellInstruction,r,child,cells,List.head?_eq_getElem?]) hi
    simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil] at hs
    refine ⟨1+t,?_,?_⟩
    · simp only [cost]; nlinarith [cost_pos q]
    · rw [show 1+t=t+1 by omega,runFrom_succ_first,hs,Option.bind_some]
      exact hr
  | load f q ih' =>
    let r : Resume P := (child P ⟨.load f q,hq⟩ q (Finset.mem_insert_of_mem Turing.TM2.stmts₁_self),f v)
    obtain ⟨t,ht,hr⟩ := ih' r.1.property r.2 S
    have hs := step_cfg (cellInstruction P) input (.exec (⟨.load f q,hq⟩,v)) ih 0 (cells P S) []
      ⟨some (.exec r),cells P S 0,.stay,.stay,none⟩ rfl hi
    simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil] at hs
    refine ⟨1+t,?_,?_⟩
    · simp only [cost]; nlinarith [cost_pos q]
    · rw [show 1+t=t+1 by omega,runFrom_succ_first,hs,Option.bind_some]
      exact hr
  | branch f q u ihq ihu =>
    by_cases hf : f v=true
    · let r : Resume P := (child P ⟨.branch f q u,hq⟩ q (Finset.mem_insert_of_mem (Finset.mem_union_left _ Turing.TM2.stmts₁_self)),v)
      obtain ⟨t,ht,hr⟩ := ihq r.1.property v S
      have hs := step_cfg (cellInstruction P) input (.exec (⟨.branch f q u,hq⟩,v)) ih 0 (cells P S) []
        ⟨some (.exec r),cells P S 0,.stay,.stay,none⟩ (by simp only [cellInstruction,hf,↓reduceIte]; rfl) hi
      simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil] at hs
      refine ⟨1+t,?_,?_⟩
      · have hm := le_max_left (cost q) (cost u)
        have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hm) (show space S+cost q+1 ≤ space S+max (cost q) (cost u)+1 by omega)
        have ht' := ht.trans hp
        simp only [cost]; nlinarith
      · rw [show 1+t=t+1 by omega,runFrom_succ_first,hs,Option.bind_some]
        simpa only [r,child,Turing.TM2.stepAux,hf,cond_true] using hr
    · have hf' : f v=false := Bool.eq_false_iff.mpr hf
      let r : Resume P := (child P ⟨.branch f q u,hq⟩ u (Finset.mem_insert_of_mem (Finset.mem_union_right _ Turing.TM2.stmts₁_self)),v)
      obtain ⟨t,ht,hr⟩ := ihu r.1.property v S
      have hs := step_cfg (cellInstruction P) input (.exec (⟨.branch f q u,hq⟩,v)) ih 0 (cells P S) []
        ⟨some (.exec r),cells P S 0,.stay,.stay,none⟩ (by simp only [cellInstruction,hf',Bool.false_eq_true,↓reduceIte]; rfl) hi
      simp only [Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil] at hs
      refine ⟨1+t,?_,?_⟩
      · have hm := le_max_right (cost q) (cost u)
        have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hm) (show space S+cost u+1 ≤ space S+max (cost q) (cost u)+1 by omega)
        have ht' := ht.trans hp
        simp only [cost]; nlinarith
      · rw [show 1+t=t+1 by omega,runFrom_succ_first,hs,Option.bind_some]
        simpa only [r,child,Turing.TM2.stepAux,hf',cond_false] using hr
  | goto f =>
    have hs := step_cfg (cellInstruction P) input (.exec (⟨.goto f,hq⟩,v)) ih 0 (cells P S) []
      ⟨some (.exec (mainResume P (f v) v)),cells P S 0,.stay,.stay,none⟩ rfl hi
    refine ⟨1,by simp [cost]; omega,?_⟩
    simpa only [runFrom,Option.bind_some,Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil,endpoint,Turing.TM2.stepAux] using hs
  | halt =>
    have hs := step_cfg (cellInstruction P) input (.exec (⟨.halt,hq⟩,v)) ih 0 (cells P S) []
      ⟨some .output,cells P S 0,.stay,.stay,none⟩ rfl hi
    refine ⟨1,by simp [cost]; omega,?_⟩
    simpa only [runFrom,Option.bind_some,Move.apply,Function.update_eq_self,Option.toList_none,List.append_nil,endpoint,Turing.TM2.stepAux] using hs

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin
open CellControl CellRoutine StackSpace

 theorem native_step_run (P : Program) (input : List Bool) (ih : ℕ) (hi : ih ≤ input.length+1)
    (c d : P.machine.tm.Cfg) (hs : P.machine.tm.step c = some d) :
    ∃ t, t ≤ 8*bound P.machine.tm*(space c.stk+bound P.machine.tm+1) ∧
      runFrom (cellInstruction P) input (endpoint P c ih) t = some (endpoint P d ih) := by
  change Turing.TM2.step P.machine.tm.m c = some d at hs
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp only [Turing.TM2.step,reduceCtorEq] at hs
  | some l =>
    change some (Turing.TM2.stepAux (P.machine.tm.m l) v S) = some d at hs
    have hd := Option.some.inj hs
    subst d
    obtain ⟨t,ht,hr⟩ := exec_run P input ih hi (P.machine.tm.m l) (main_mem P l) v S
    refine ⟨t,?_,hr⟩
    change t ≤ 8*bound P.machine.tm*(space S+bound P.machine.tm+1)
    have hc := cost_le_bound P.machine.tm l
    exact ht.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hc) (by omega))

 theorem run_iter (tm : Turing.FinTM2) (c : tm.Cfg) (t : ℕ) :
    StackSpace.run tm c t = (fun x : Option tm.Cfg => x.bind tm.step)^[t] (some c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [StackSpace.run,ih,Function.iterate_succ_apply']

 theorem native_run (P : Program) (input : List Bool) (H t : ℕ) (htH : t ≤ H)
    (c : P.machine.tm.Cfg)
    (hr : StackSpace.run P.machine.tm (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) t = some c) :
    ∃ s, s ≤ (8*bound P.machine.tm*(input.length+bound P.machine.tm*H+bound P.machine.tm+1))*t ∧
      runFrom (cellInstruction P) input
        (endpoint P (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) (input.length+1)) s =
      some (endpoint P c (input.length+1)) := by
  induction t generalizing c with
  | zero =>
    have he := Option.some.inj hr
    subst c
    exact ⟨0,by simp,rfl⟩
  | succ t ih' =>
    cases he : StackSpace.run P.machine.tm (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) t with
    | none => simp only [StackSpace.run,he,Option.bind_none,reduceCtorEq] at hr
    | some d =>
      have hs : P.machine.tm.step d = some c := by simpa only [StackSpace.run,he,Option.bind_some] using hr
      obtain ⟨s1,hs1,hr1⟩ := ih' (by omega) d he
      obtain ⟨s2,hs2,hr2⟩ := native_step_run P input (input.length+1) (by omega) d c hs
      have hd := input_run_space P.machine.tm (input.map P.machine.inputAlphabet.symm) t d he
      simp only [List.length_map] at hd
      have hmul : bound P.machine.tm*t ≤ bound P.machine.tm*H := Nat.mul_le_mul_left _ (by omega)
      have hs2' : s2 ≤ 8*bound P.machine.tm*(input.length+bound P.machine.tm*H+bound P.machine.tm+1) :=
        hs2.trans (Nat.mul_le_mul_left _ (by omega))
      refine ⟨s1+s2,?_,runFrom_trans _ _ _ _ _ _ _ hr1 hr2⟩
      rw [Nat.mul_succ]
      omega

 theorem polynomial_envelope (B L T : ℕ) :
    2*L+3 + (8*B*(L+B*T+B+1))*T + (L+B*T)+1 ≤
      (8*B*(B+2)+B+8)*(T+L+1)^2 := by
  let z := T+L+1
  have hz : 1 ≤ z := by dsimp [z]; omega
  have hT : T ≤ z := by dsimp [z]; omega
  have hL : L ≤ z := by dsimp [z]; omega
  have hW : L+B*T+B+1 ≤ (B+2)*z := by dsimp [z]; nlinarith
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left (8*B) hW) hT
  have hsmall : 2*L+3+(L+B*T)+1 ≤ (B+8)*z := by dsimp [z]; nlinarith
  have hzsq : z ≤ z^2 := by nlinarith
  have hhsmall := hsmall.trans (Nat.mul_le_mul_left (B+8) hzsq)
  calc
    _ = (8*B*(L+B*T+B+1))*T + (2*L+3+(L+B*T)+1) := by omega
    _ ≤ 8*B*((B+2)*z)*z + (B+8)*z^2 := Nat.add_le_add hprod hhsmall
    _ = _ := by dsimp only [z]; ring

end EdgeSublinearMWIS.Main.StackCompiler
end

noncomputable section

open scoped Classical
open CatalyticMatching.General
set_option autoImplicit false
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.StackCompiler EdgeSublinearMWIS.Main.StackSpace
open EdgeSublinearMWIS.Main.CellControl EdgeSublinearMWIS.Main.CellRoutine

theorem solution :
    ∃ q : ℕ, 0 < q ∧ ∀ P : Program,
      ∃ (M : Machine) (K : ℕ), 0 < K ∧
        ∀ (input output : List Bool) (t : ℕ), Runs P input output t →
          ∃ s : ℕ, BitHalts M input output s ∧ s ≤ K * (t + input.length + 1) ^ q := by
  refine ⟨2,by decide,?_⟩
  intro P
  let B := bound P.machine.tm
  let F := 5*CellBitCode.width (A := Cell P)+3
  let K0 := 8*B*(B+2)+B+8
  let M := CellBitCode.compile (blank P) CellState.initStart (cellInstruction P)
  refine ⟨M,F*K0,by dsimp [F,K0]; positivity,?_⟩
  intro input output t hRuns
  change Nonempty (Turing.TM2OutputsInTime P.machine.tm
    (input.map P.machine.inputAlphabet.symm) (some (output.map P.machine.outputAlphabet.symm)) t) at hRuns
  obtain ⟨h⟩ := hRuns
  let final := Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)
  have hn : StackSpace.run P.machine.tm
      (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) h.steps = some final := by
    rw [run_iter]
    exact h.evals_in_steps
  have hsteps : h.steps ≤ t := h.steps_le_m
  have hspace := input_run_space P.machine.tm (input.map P.machine.inputAlphabet.symm) h.steps final hn
  simp only [List.length_map] at hspace
  have hlength : output.length ≤ input.length+B*t := by
    have hl := stack_length_le_space final.stk P.machine.tm.k₁
    have he : final.stk P.machine.tm.k₁=output.map P.machine.outputAlphabet.symm := by simp [final,Turing.haltList]
    rw [he,List.length_map] at hl
    exact (hl.trans hspace).trans (Nat.add_le_add_left (Nat.mul_le_mul_left B hsteps) _)
  obtain ⟨s0,hs0,hr0⟩ := native_run P input t h.steps hsteps final hn
  have hs0' : s0 ≤ (8*B*(input.length+B*t+B+1))*t := hs0.trans (Nat.mul_le_mul_left _ hsteps)
  have hInit := initialize_run P input
  have h01 := runFrom_trans _ _ _ _ _ _ _ hInit hr0
  have htrack : ∀ i, cells P final.stk (0+i) P.machine.tm.k₁ = (output.map P.machine.outputAlphabet.symm)[i]? := by
    intro i
    simp [cells,final,Turing.haltList]
  have hOut := output_run P input (input.length+1) 0 (cells P final.stk) []
    (output.map P.machine.outputAlphabet.symm) (by omega) htrack
  simp only [List.length_map,Nat.zero_add,List.map_map,Function.comp_def,Equiv.apply_symm_apply,List.map_id_fun',List.append_nil,List.nil_append] at hOut
  have hCell := runFrom_trans _ _ _ _ _ _ _ h01 hOut
  have hTime : (2*input.length+3)+s0+(output.length+1) ≤ K0*(t+input.length+1)^2 := by
    calc
      _ ≤ 2*input.length+3 + (8*B*(input.length+B*t+B+1))*t + (input.length+B*t)+1 := by omega
      _ ≤ _ := polynomial_envelope B input.length t
  obtain ⟨s,hs,hhalt⟩ := CellBitCode.compile_halts (blank P) CellState.initStart (cellInstruction P)
    input output ((2*input.length+3)+s0+(output.length+1)) _ hCell rfl rfl
  refine ⟨s,hhalt,?_⟩
  exact hs.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left F hTime)
end
