-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja22_original_finite_cutoff_strip_exact_square_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:38:08.8252+00:00
-- url     : https://prove2.me/submissions/62d61c9e-605f-4108-9eff-f07c2d2b349f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_strip
import Theorems.Thm_AvramDividend_Classical_avram_ja23_original_marked_strip_compensated_l2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The exact original cutoff difference is the centred signed physical strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioc
          (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν) := by
  intro n m hnm t
  let S : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let C : Ω → ℝ := fun ω =>
    (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
      (t : ℝ) * (∫ z in S, z ∂X.ν)
  let F : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
      avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω
  have hEq : F = C := by
    funext ω
    exact (avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
      X n m t ω).trans
      (avram_p4_h_gaussian_original_smalljump_cutoff_strip X n m hnm t ω)
  have hL2 :=
    avram_ja23_original_marked_strip_compensated_l2 X hX hFinite n m hnm t
  change Integrable (fun ω => (C ω) ^ 2) P ∧
    (∫ ω, (C ω) ^ 2 ∂P) =
      (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν) at hL2
  rw [← hEq] at hL2
  simpa only [F, S] using hL2
