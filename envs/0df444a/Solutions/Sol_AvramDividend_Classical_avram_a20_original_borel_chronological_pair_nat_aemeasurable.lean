-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_chronological_pair_nat_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:42:20.809935+00:00
-- url     : https://prove2.me/submissions/544c9c05-0e96-4bfc-a080-3501dd7384f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_factorial_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_factorial_physical_pair_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_nat_pair_ennreal_aemeasurable_from_real_integrable
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
    let K : Ω → ℕ := fun ω => ((S ω ×ˢ S ω) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    AEMeasurable (fun ω => (K ω : ℝ≥0∞)) P := by
  intro S K
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  have hFI : Integrable
      (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P := by
    simpa only [N] using
      (avram_a20_original_negative_borel_factorial_integrable
        X hFinite T B hB hNeg)
  have hPair : ∀ᵐ ω ∂P,
      (N ω).toReal * ((N ω).toReal - 1) =
        2 * (K ω : ℝ) := by
    simpa only [N, S, K] using
      (avram_a20_original_borel_factorial_physical_pair_ae
        X hFinite T B hB hNeg)
  exact avram_a20_nat_pair_ennreal_aemeasurable_from_real_integrable
    P K (hFI.congr hPair)
