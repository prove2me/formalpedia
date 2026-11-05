-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_global_step_error_from_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:20:08.557204+00:00
-- url     : https://prove2.me/submissions/e048ae9d-9570-4771-b432-48a64ab470fe

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_monotone_cuts_cover_interval
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_ordered_step_interior_modulus_error
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_step_sum_vanishes_outside_cut_span

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped BigOperators

/-- An ordered compact-test step approximation has global error control. -/
theorem solution {n : ℕ} (f : ℝ → ℝ) (p : Fin (n + 1) → ℝ)
    (δ η : ℝ) (hη : 0 < η) (hp : StrictMono p)
    (hwidth : ∀ i : Fin n, p i.succ - p i.castSucc < δ)
    (hmod : ∀ x y : ℝ, |x - y| < δ → |f x - f y| < η)
    (hleft : ∀ z : ℝ, z ≤ p 0 → f z = 0)
    (hright : ∀ z : ℝ, p (Fin.last n) < z → |f z| ≤ η) :
    ∀ z : ℝ, |f z - (∑ i : Fin n,
      if z ∈ Ioc (p i.castSucc) (p i.succ)
      then f (p i.castSucc) else 0)| ≤ η := by
  classical
  have hordered : ∀ i j : Fin n, i < j → p i.succ ≤ p j.castSucc := by
    intro i j hij
    apply hp.monotone
    apply Fin.le_iff_val_le_val.mpr
    have hv : i.val < j.val := hij
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  intro z
  by_cases hzleft : z ≤ p 0
  · have hsum := avram_p2_l_mesh_step_sum_vanishes_outside_cut_span
      p (fun i : Fin n => f (p i.castSucc)) hp.monotone z (Or.inl hzleft)
    calc
      |f z - (∑ i : Fin n,
        if z ∈ Ioc (p i.castSucc) (p i.succ)
        then f (p i.castSucc) else 0)| = |f z| := by rw [hsum, sub_zero]
      _ = 0 := by rw [hleft z hzleft, abs_zero]
      _ ≤ η := le_of_lt hη
  · by_cases hzright : z ≤ p (Fin.last n)
    · obtain ⟨i, hi⟩ := avram_p2_l_mesh_finite_monotone_cuts_cover_interval
        p z (lt_of_not_ge hzleft) hzright
      exact le_of_lt (avram_p2_l_mesh_ordered_step_interior_modulus_error
        f (fun i : Fin n => p i.castSucc) (fun i => p i.succ)
        hordered δ η hmod hwidth z i hi)
    · have htail : p (Fin.last n) < z := lt_of_not_ge hzright
      have hsum := avram_p2_l_mesh_step_sum_vanishes_outside_cut_span
        p (fun i : Fin n => f (p i.castSucc)) hp.monotone z (Or.inr htail)
      calc
        |f z - (∑ i : Fin n,
          if z ∈ Ioc (p i.castSucc) (p i.succ)
          then f (p i.castSucc) else 0)| = |f z| := by rw [hsum, sub_zero]
        _ ≤ η := hright z htail
