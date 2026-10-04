-- Prove2me | solution 1 for Combinatorics.uniform_family_monochromatic_event_independence
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:09:04.454831+00:00
-- url     : https://prove2.me/submissions/a8e01170-e3cb-4c9d-9437-f2317e258859

import Mathlib

set_option autoImplicit false

section Helpers7dc

/-- If the left numerator vanishes while every other count is positive, the claimed
product identity `a/N = g/N * c/N` fails. -/
theorem key_nat_7dc (a g c N : ℕ) (ha : a = 0) (hg : 0 < g) (hc : 0 < c) (hN : 0 < N) :
    ¬ ((a : ℝ) / (N : ℝ) = (g : ℝ) / (N : ℝ) * (c : ℝ) / (N : ℝ)) := by
  subst ha
  intro h
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (g : ℝ) / (N : ℝ) * (c : ℝ) / (N : ℝ) := by positivity
  simp only [Nat.cast_zero, zero_div] at h
  linarith

end Helpers7dc

theorem solution : ¬ (∀ (X I : Type) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (B : I -> Finset X) (m D : Nat)
    (hm : 0 < m) (hsize : forall i, (B i).card = m)
    (hdegree : forall x, (Finset.univ.filter (fun i => Membership.mem (B i) x)).card <= D),
    (let A : I -> Finset (X -> Bool) := fun i =>
      Finset.univ.filter (fun c =>
        (forall x, Membership.mem (B i) x -> c x = true) \/
        (forall x, Membership.mem (B i) x -> c x = false))
     let dep : I -> I -> Prop := fun i j =>
       i != j /\ Exists fun x => Membership.mem (B i) x /\ Membership.mem (B j) x
     (forall (i : I) (S : Finset I),
       (forall j, Membership.mem S j -> Not (dep i j)) ->
       ((Finset.filter (fun w => Membership.mem (A i) w)
           (Finset.univ.filter (fun w => forall j, Membership.mem S j ->
             Not (Membership.mem (A j) w)))).card : Real) /
           (Fintype.card (X -> Bool) : Real) =
         (((Finset.univ.filter (fun w => forall j, Membership.mem S j ->
             Not (Membership.mem (A j) w))).card : Real) /
             (Fintype.card (X -> Bool) : Real)) *
           ((A i).card : Real) / (Fintype.card (X -> Bool) : Real)))) := by
  intro h
  have h1 := h (Fin 2) Unit (fun _ => Finset.univ) 2 1 (by norm_num)
    (fun _ => by simp) (fun x => by simp)
  dsimp only at h1
  refine key_nat_7dc _ _ _ _ ?_ ?_ ?_ ?_ (h1 () {()} ?_)
  · refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
    intro w hw hA
    exact (Finset.mem_filter.mp hw).2 () (Finset.mem_singleton_self _) hA
  · refine Finset.card_pos.mpr ⟨![true, false], ?_⟩
    simp [Fin.forall_fin_two]
  · refine Finset.card_pos.mpr ⟨fun _ => true, ?_⟩
    simp
  · exact Fintype.card_pos
  · intro j _ hd
    cases j
    simp at hd
