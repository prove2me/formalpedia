-- Prove2me | solution 2 for AvramDividend.Classical.avram_a20_original_borel_chronological_pair_mean_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:42:30.481292+00:00
-- url     : https://prove2.me/submissions/7467dcf9-ff23-4c0e-b8e6-efeea2c35c98

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_chronological_pair_nat_aemeasurable
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_pair_lintegral_all_horizons
import Theorems.Thm_AvramDividend_Classical_avram_a20_finite_ennreal_quadratic_rate_to_real
import Theorems.Thm_AvramDividend_Classical_avram_a20_generic_integrable_real_pair_of_nat_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let S : Ω → Set ℝ≥0 := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : Ω → ℕ := fun ω =>
      ((S ω ×ˢ S ω) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
      (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let S : Ω → Set ℝ≥0 := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  let S₀ : Ω → Set ℝ≥0 := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  let K : Ω → ℕ := fun ω => ((S ω ×ˢ S ω) ∩
    {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
  let K₀ : Ω → ℕ := fun ω => ((S₀ ω ×ˢ S₀ ω) ∩
    {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2
  have hKmeas : AEMeasurable (fun ω => (K ω : ℝ≥0∞)) P := by
    simpa only [S, K] using
      (avram_a20_original_borel_chronological_pair_nat_aemeasurable
        X hFinite T B hB hNeg)
  have hSets (ω : Ω) : S ω = S₀ ω := by
    ext u
    simp only [S, S₀, Set.mem_setOf_eq]
    tauto
  have hK (ω : Ω) : K ω = K₀ ω := by
    change ((S ω ×ˢ S ω) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard =
      ((S₀ ω ×ˢ S₀ ω) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    rw [hSets ω]
  have hMean₀ : (∫⁻ ω, (K₀ ω : ℝ≥0∞) ∂P) =
      (((T : ℝ≥0∞) * X.ν B) ^ 2) / 2 := by
    simpa only [S₀, K₀] using
      (avram_a20_original_borel_pair_lintegral_all_horizons
        X hFinite T B hB hNeg)
  have hν : X.ν B < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
  have hRate : ((T : ℝ≥0∞) * X.ν B) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.coe_lt_top hν
  have hMean : (∫⁻ ω, (K ω : ℝ≥0∞) ∂P) =
      ENNReal.ofReal (r ^ 2 / 2) := by
    calc
      (∫⁻ ω, (K ω : ℝ≥0∞) ∂P) =
          (∫⁻ ω, (K₀ ω : ℝ≥0∞) ∂P) := by
            apply lintegral_congr
            intro ω
            rw [hK ω]
      _ = (((T : ℝ≥0∞) * X.ν B) ^ 2) / 2 := hMean₀
      _ = ENNReal.ofReal (r ^ 2 / 2) := by
        simpa only [r] using
          (avram_a20_finite_ennreal_quadratic_rate_to_real
            ((T : ℝ≥0∞) * X.ν B) hRate)
  exact avram_a20_generic_integrable_real_pair_of_nat_lintegral
    P K r hKmeas hMean
