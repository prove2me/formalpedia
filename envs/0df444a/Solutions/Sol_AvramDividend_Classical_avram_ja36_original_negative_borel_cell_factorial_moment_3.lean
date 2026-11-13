-- Prove2me | solution 3 for AvramDividend.Classical.avram_ja36_original_negative_borel_cell_factorial_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:38:02.158458+00:00
-- url     : https://prove2.me/submissions/5cbab2fa-f631-4b74-b005-80e0bcf1760a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_factorial_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_factorial_physical_pair_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_chronological_pair_mean_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Reduce the original marked-count factorial moment to genuine chronological pair compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let J : Ω → ℝ := fun ω => (N ω).toReal
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => J ω * (J ω - 1)) P ∧
      (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2 := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let J : Ω → ℝ := fun ω => (N ω).toReal
  let S : Ω → Set ℝ≥0 := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  let K : Ω → ℕ := fun ω =>
    ((S ω ×ˢ S ω) ∩ {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => J ω * (J ω - 1)) P ∧
    (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2
  have hI : Integrable (fun ω => J ω * (J ω - 1)) P := by
    simpa only [N, J] using
      (avram_a20_original_negative_borel_factorial_integrable X hFinite T B hB hNeg)
  have hAE : ∀ᵐ ω ∂P, J ω * (J ω - 1) = 2 * (K ω : ℝ) := by
    simpa only [N, J, S, K] using
      (avram_a20_original_borel_factorial_physical_pair_ae X hFinite T B hB hNeg)
  have hPairs :
      Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
        (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by
    simpa only [S, K, r] using
      (avram_a20_original_borel_chronological_pair_mean_exact X hFinite T B hB hNeg)
  exact ⟨hI, (integral_congr_ae hAE).trans hPairs.2⟩
