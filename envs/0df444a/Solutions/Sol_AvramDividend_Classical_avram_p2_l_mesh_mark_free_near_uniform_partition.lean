-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_mark_free_near_uniform_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:14:12.842702+00:00
-- url     : https://prove2.me/submissions/aa0ad082-832b-452d-9ca5-cb78560fc4e8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_nominal_cuts_geometry
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_ordered_mark_avoiding_perturbations
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_perturbed_successor_gap_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Uniform nominal cuts can all avoid finitely many marks while staying fine. -/
theorem solution (S : Finset ℝ) (n : ℕ) (A h r : ℝ)
    (hh : 0 < h) (hr : 0 < r) (hsep : 2 * r ≤ h) :
    ∃ p : Fin (n + 1) → ℝ, StrictMono p ∧
      (∀ i : Fin (n + 1),
        |p i - (A + (i.val : ℝ) * h)| < r ∧ p i ∉ S) ∧
      (∀ i : Fin n, p i.succ - p i.castSucc < h + 2 * r) := by
  let x : Fin (n + 1) → ℝ := fun i => A + (i.val : ℝ) * h
  obtain ⟨hxmono, hxgap, hxfirst, hxlast⟩ :=
    avram_p2_l_mesh_uniform_nominal_cuts_geometry n A h hh
  have hwindow : ∀ i j : Fin (n + 1),
      i < j → x i + r ≤ x j - r := by
    intro i j hij
    have hnat : i.val + 1 ≤ j.val :=
      Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hij)
    have hreal : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal (le_of_lt hh)
    dsimp [x]
    nlinarith
  obtain ⟨p, hpnear, hpmono⟩ :=
    avram_p2_l_mesh_ordered_mark_avoiding_perturbations
      S x r hr hwindow
  have hpwidth : ∀ i : Fin n,
      p i.succ - p i.castSucc < h + 2 * r := by
    apply avram_p2_l_mesh_perturbed_successor_gap_bound x p r h
    · exact fun i => (hpnear i).1
    · intro i
      exact le_of_eq (hxgap i)
  refine ⟨p, hpmono, ?_, hpwidth⟩
  simpa only [x] using hpnear
