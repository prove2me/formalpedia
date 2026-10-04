-- Prove2me | solution 1 for CookPvsNP.stack_cleanup
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T12:09:35.876276+00:00
-- url     : https://prove2.me/submissions/cd0cb1e7-1813-4cb1-ad0f-0517614b4754

import Definitions.Def_CookPvsNP_StackRepresentation

set_option autoImplicit false
open CookPvsNP

section
variable {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
  [DecidableEq K] [DecidableEq A] [DecidableEq Q]
  (P : StackMachine K A Q) (ki ko : K)
local notation "M" => stackTM P ki ko

private theorem scan (r : List (StackCol K A)) (L : List (Option (StackSym K A))) :
    (M).run r.length
      ⟨.clean, L, (r.map (some ∘ StackSym.work)).headD none,
        (r.map (some ∘ StackSym.work)).tail⟩ =
      ⟨.clean, (r.map (fun x => (x ko).map StackSym.output)).reverse ++ L, none, []⟩ := by
  induction r generalizing L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.headD_cons, List.tail_cons]
    have hs : (M).step ⟨.clean, L, some (.work x), xs.map (some ∘ StackSym.work)⟩ =
        ⟨.clean, (x ko).map StackSym.output :: L,
          (xs.map (some ∘ StackSym.work)).headD none,
          (xs.map (some ∘ StackSym.work)).tail⟩ := by
      simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((M).step^[xs.length]) hs).trans ?_
    simpa [TM.run, List.reverse_cons, List.append_assoc] using
      ih ((x ko).map StackSym.output :: L)

private theorem back (r : List (Option A)) (R : List (Option (StackSym K A))) :
    (M).run r.length
      ⟨.cleanBack, (r.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (r.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).headD none, R⟩ =
      ⟨.cleanBack, [], some (StackSym.origin (K := K) (A := A)), (r.map (Option.map StackSym.output)).reverse ++ R⟩ := by
  induction r generalizing R with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, TM.run, Function.iterate_succ_apply, List.map_cons,
      List.cons_append, List.headD_cons, List.tail_cons]
    have hs : (M).step
        ⟨.cleanBack, xs.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))],
          x.map StackSym.output, R⟩ =
        ⟨.cleanBack, (xs.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
          (xs.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
          x.map StackSym.output :: R⟩ := by
      cases x <;> cases xs <;> simp [TM.step, TM.IsHalting, stackTM]
    refine (congrArg ((M).step^[xs.length]) hs).trans ?_
    simpa [TM.run, List.reverse_cons, List.append_assoc] using ih (x.map StackSym.output :: R)

end

theorem solution {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q)
    (x : StackCol K A) (xs : List (StackCol K A)) (hq : P.done q = true) :
    let out := (x :: xs).map (fun v => (v ko).map (StackSym.output (K := K))) ++ [none]
    (stackTM P ki ko).run (2 * (x :: xs).length + 2) (stackFrame q (x :: xs)) =
      ⟨.accept, [some (StackSym.origin (K := K) (A := A))], out.headD none, out.tail⟩ := by
  let M := stackTM P ki ko
  let ys := (x :: xs).map (fun v => v ko)
  let out := ys.map (Option.map (StackSym.output (K := K))) ++ [none]
  have hfirst : (M).run 1 (stackFrame q (x :: xs)) =
      ⟨.clean, (x ko).map StackSym.output :: [some (StackSym.origin (K := K) (A := A))],
        (xs.map (some ∘ StackSym.work)).headD none,
        (xs.map (some ∘ StackSym.work)).tail⟩ := by
    simp [M, TM.run, TM.step, TM.IsHalting, stackTM, stackFrame, hq]
  have hr := scan P ki ko xs [(x ko).map StackSym.output, some (StackSym.origin (K := K) (A := A))]
  have hb : (M).run 1
      ⟨.clean, (ys.map (Option.map StackSym.output)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ =
      ⟨.cleanBack,
        (ys.reverse.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (ys.reverse.map (Option.map StackSym.output) ++ [some (StackSym.origin (K := K) (A := A))]).headD none,
        [none]⟩ := by
    cases h : ys.reverse <;> simp [M, TM.run, TM.step, TM.IsHalting, stackTM, ← List.map_reverse, h]
  have hl := back P ki ko ys.reverse [none]
  have hf : (M).run 1 ⟨.cleanBack, [], some (StackSym.origin (K := K) (A := A)), out⟩ =
      ⟨.accept, [some (StackSym.origin (K := K) (A := A))], out.headD none, out.tail⟩ := by
    simp [M, TM.run, TM.step, TM.IsHalting, stackTM]
  have hr' : (M).run xs.length ((M).run 1 (stackFrame q (x :: xs))) =
      ⟨.clean, (ys.map (Option.map StackSym.output)).reverse ++ [some (StackSym.origin (K := K) (A := A))], none, []⟩ := by
    exact (congrArg ((M).run xs.length) hfirst).trans
      (by simpa [M, ys, List.reverse_cons, List.append_assoc, List.map_map, Function.comp_def] using hr)
  simp only [List.length_reverse, List.map_reverse, List.reverse_reverse] at hl
  simp only [List.map_reverse] at hb
  have hn : ys.length = (x :: xs).length := List.length_map _
  rw [hn] at hl
  have h2 := (congrArg ((M).run 1) hr').trans hb
  have h3 := (congrArg ((M).run (x :: xs).length) h2).trans hl
  have h4 := (congrArg ((M).run 1) h3).trans hf
  have ht : 1 + ((x :: xs).length + (1 + (xs.length + 1))) = 2 * (x :: xs).length + 2 := by simp; omega
  have hmain : (M).run (2 * (x :: xs).length + 2) (stackFrame q (x :: xs)) =
      ⟨.accept, [some (StackSym.origin (K := K) (A := A))], out.headD none, out.tail⟩ := by
    unfold TM.run at h4 ⊢
    dsimp only [M, stackTM] at h4 ⊢
    rw [← ht, Function.iterate_add_apply, Function.iterate_add_apply,
      Function.iterate_add_apply, Function.iterate_add_apply]
    exact h4
  simpa only [out, ys, List.map_map, Function.comp_def] using hmain

#print axioms solution
