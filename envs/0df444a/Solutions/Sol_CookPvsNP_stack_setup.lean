-- Prove2me | solution 1 for CookPvsNP.stack_setup
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T11:47:07.631532+00:00
-- url     : https://prove2.me/submissions/195ed9c2-a46d-481e-adb6-db1c3f8c8566

import Definitions.Def_CookPvsNP_StackCompiler

set_option autoImplicit false
open CookPvsNP

section
variable {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
  [DecidableEq K] [DecidableEq A] [DecidableEq Q]
  (P : StackMachine K A Q) (ki ko : K)
local notation "M" => stackTM P ki ko

private theorem scan (w : List A) (L : List (Option (StackSym K A))) :
    (M).run w.length
      ⟨.setup, L, (w.map (some ∘ StackSym.input)).headD none,
        (w.map (some ∘ StackSym.input)).tail⟩ =
      ⟨.setup, (w.map (fun b => some (.work (stackInitialCol ki b)))).reverse ++ L, none, []⟩ := by
  induction w generalizing L with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.headD_cons, List.tail_cons]
    have hs : (M).step ⟨.setup, L, some (.input b), bs.map (some ∘ StackSym.input)⟩ =
        ⟨.setup, some (.work (stackInitialCol ki b)) :: L,
          (bs.map (some ∘ StackSym.input)).headD none,
          (bs.map (some ∘ StackSym.input)).tail⟩ := by
      simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((M).step^[bs.length]) hs).trans ?_
    simpa [TM.run, List.reverse_cons, List.append_assoc] using
      ih (some (.work (stackInitialCol ki b)) :: L)

private theorem back (r : List (StackCol K A)) (R : List (Option (StackSym K A))) :
    (M).run r.length
      ⟨.setupBack, (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none, R⟩ =
      ⟨.setupBack, [], some (StackSym.origin (K := K) (A := A)), (r.map (some ∘ StackSym.work)).reverse ++ R⟩ := by
  induction r generalizing R with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs : (M).step
        ⟨.setupBack, xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))],
          some (.work x), R⟩ =
        ⟨.setupBack, (xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
          (xs.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
          some (.work x) :: R⟩ := by
      cases xs <;> simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((M).step^[xs.length]) hs).trans ?_
    simpa [TM.run, List.reverse_cons, List.append_assoc] using ih (some (.work x) :: R)

end

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (w : List A) :
    (stackTM P ki ko).run (2 * w.length + 4)
      ((stackTM P ki ko).init (w.map stackInput)) =
      stackFrame P.initial (w.map (stackInitialCol ki) ++ [stackZero]) := by
  let M := stackTM P ki ko
  let r := w.map (stackInitialCol ki)
  have hs : (M).run 2 ((M).init (w.map stackInput)) =
      ⟨.setup, [some (StackSym.origin (K := K) (A := A))], (w.map (some ∘ StackSym.input)).headD none,
        (w.map (some ∘ StackSym.input)).tail⟩ := by
    cases w <;> simp [M, TM.run, TM.init, Function.iterate_succ_apply,
      TM.step, TM.IsHalting, stackTM, stackInput, List.map_map, Function.comp_def, Function.Embedding.coeFn_mk]
    exact ⟨rfl, fun _ _ => rfl⟩
  have hr := scan P ki ko w [some (StackSym.origin (K := K) (A := A))]
  have hb : (M).run 1
      ⟨.setup, (r.map (some ∘ StackSym.work)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ =
      ⟨.setupBack, (r.reverse.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (r.reverse.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
        [some (.work stackZero)]⟩ := by
    cases h : r.reverse <;>
      simp [M, TM.run, TM.step, TM.IsHalting, stackTM, ← List.map_reverse, h]
  have hl := back P ki ko r.reverse [some (.work stackZero)]
  have hf : (M).run 1
      ⟨.setupBack, [], some (StackSym.origin (K := K) (A := A)), r.map (some ∘ StackSym.work) ++ [some (.work stackZero)]⟩ =
      stackFrame P.initial (r ++ [stackZero]) := by
    simp [M, TM.run, TM.step, TM.IsHalting, stackTM, stackFrame]
  simp only [List.length_reverse, List.map_reverse, List.reverse_reverse] at hl
  simp only [List.map_reverse] at hb
  have hn : r.length = w.length := List.length_map _
  rw [hn] at hl
  have he : w.map (fun b => some (StackSym.work (stackInitialCol ki b))) =
      r.map (some ∘ StackSym.work) := by simp [r, List.map_map, Function.comp_def]
  rw [he] at hr
  have h1 := (congrArg ((M).run w.length) hs).trans hr
  have h2 := (congrArg ((M).run 1) h1).trans hb
  have h3 := (congrArg ((M).run w.length) h2).trans hl
  have h4 := (congrArg ((M).run 1) h3).trans hf
  have ht : 1 + (w.length + (1 + (w.length + 2))) = 2 * w.length + 4 := by omega
  simpa only [TM.run, ← Function.iterate_add_apply, ht] using h4

#print axioms solution
