-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_negative_jumps_joint_marked_pgf_as_finite_product_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:08:39.028927+00:00
-- url     : https://prove2.me/submissions/89c16f61-da91-49db-80b7-008a9f99aa81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_a27_finite_marked_count_exp_weight_product_factor_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ z : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      K ω = S.card ∧
      z ^ (K ω) * Real.exp (θ * J ω) =
        ∏ u ∈ S, z * Real.exp (θ *
          (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
  have hCountFin :=
    avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
      X hFinite t (Iio (0 : ℝ)) measurableSet_Iio Subset.rfl
      K hK hCount
  have hProd :=
    avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
      X hFinite t θ J hJEq
  filter_upwards [hCountFin, hProd] with ω hC hP
  obtain ⟨S, hS, hCard⟩ := hC
  obtain ⟨S', hS', hExp⟩ := hP
  have hSS' : S = S' := by
    apply Finset.ext
    intro u
    constructor
    · intro hu
      rcases (hS u).mp hu with ⟨huPos, huT, huNZ, _⟩
      exact (hS' u).mpr ⟨huPos, huT, huNZ⟩
    · intro hu
      rcases (hS' u).mp hu with ⟨huPos, huT, huNZ⟩
      have hLE :=
        avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u huPos
      have hLT : X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 :=
        lt_of_le_of_ne hLE huNZ
      exact (hS u).mpr ⟨huPos, huT, huNZ, hLT⟩
  have hSimple :
      Real.exp (θ * J ω) =
        ∏ u ∈ S', Real.exp (θ *
          (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
    rw [hExp]
    apply Finset.prod_congr rfl
    intro u hu
    have huT := ((hS' u).mp hu).2.1
    simp [huT]
  refine ⟨S', hS', ?_, ?_⟩
  · simpa [hSS'] using hCard
  · rw [← hSS'] at hSimple ⊢
    rw [hCard, hSimple]
    exact AvramDividend.Classical.avram_a27_finite_marked_count_exp_weight_product_factor_20261117
      S z θ (fun u => X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
