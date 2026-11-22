-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_finite_horizon_jump_series_is_source_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:11:38.162134+00:00
-- url     : https://prove2.me/submissions/8ca29eff-f9de-465a-b572-06ca9a17dc47

/- Original source physical finite jump series equals finite causal
   marked sum. Reuses source a88 actual jump support and proved a35
   finite-support tsum identity. No replacement random process. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
      (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
      J ω = ∑ u ∈ S,
        (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u) := by
  have hFiniteSupport :=
    avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
      X hFinite t (0 : ℝ) J hJEq
  filter_upwards [hJEq, hFiniteSupport] with ω hJ ⟨S, hS, _⟩
  refine ⟨S, hS, ?_⟩
  calc
    J ω =
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) := hJ
    _ = ∑ u ∈ S, if u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0 := by
      exact avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
        (fun u => X.X u ω -
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)
        t S hS t le_rfl
    _ = ∑ u ∈ S,
          (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [((hS u).mp hu).2.1]

