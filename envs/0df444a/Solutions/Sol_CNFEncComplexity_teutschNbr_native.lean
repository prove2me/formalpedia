-- Prove2me | solution 1 for CNFEncComplexity.teutschNbr_native
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T06:55:49.792521+00:00
-- url     : https://prove2.me/submissions/2e6edecb-a047-4197-bc1d-2f257128bf59

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
        | none => []
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
  let no : Query → List Bool := fun _ => []
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
            | none => []
            | some w => true :: w.bits) = (if q then true :: z.bits else []) by
        exact this _ _
      intro q _ z
      by_cases hq : q <;> simp [hq]
    · simp [encBits, mergeNbr, ramFoldedLayer, houter, hleft, valid, no,
        j, degree, n, logN, N, k, l, i]
  · have hvalidFalse : ¬ valid (N₀,k₀,l₀,i₀) := fun h => houter ⟨h.1, h.2.1⟩
    rw [if_neg hvalidFalse]
    simp [encBits, mergeNbr, houter, no, j, degree, n, logN, N, i]

end CNFEncComplexity

namespace CNFEncComplexity
open Turing.MultiTapeTM

theorem _root_.solution (P : TimeSpaceMA.Program) (e C a : ℕ) :
    ComputableTidilyInPolyTime
      (mergeNbr (fun N => a * (Nat.log 2 N + 1)^a) (ramFoldedLayer P e C))
      (encPair encNat (encPair encNat (encPair encNat encNat))) (encOption encNat) := by
  apply (teutschNbr_tidy P e C a (TimeSpaceMA.shortRun_polytime P)
    TimeSpaceMA.sparseRead_polytime).of_enc_eq
  intro x
  cases h : mergeNbr (fun N => a * (Nat.log 2 N + 1)^a) (ramFoldedLayer P e C) x <;>
    simp [h, encOption_none, encOption_some, encNat_apply, encBits]

end CNFEncComplexity
