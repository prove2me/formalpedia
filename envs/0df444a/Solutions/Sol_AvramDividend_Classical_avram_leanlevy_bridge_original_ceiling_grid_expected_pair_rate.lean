-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_ceiling_grid_expected_pair_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:58:03.638917+00:00
-- url     : https://prove2.me/submissions/d54fbc95-d3f7-4116-88b9-f3e1cf0de577

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_rate_sum_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k)
    (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i) (htT : ∀ i, t i ≤ T)
    (hs : ∀ i, (s i : ℝ) = (i.val : ℝ) * (T : ℝ) / (k : ℝ))
    (ht : ∀ i, (t i : ℝ) = ((i.val + 1 : ℕ) : ℝ) * (T : ℝ) / (k : ℝ)) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    (∫⁻ ω, (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)) ∂P) =
      ∑ i : Fin k, (((s i : ℝ≥0) : ℝ≥0∞) * X.ν B) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  classical
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B)
  have hPoint (ω : Ω) :
      (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)) =
      ∑ i : Fin k, N 0 (s i) ω * N (s i) (t i) ω := by
    simpa only [F, B, N] using
      (avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
        X T hT n k hk s t hst htT hs ht ω)
  have hExpected :
      (∫⁻ ω, ∑ i : Fin k, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin k, (((s i : ℝ≥0) : ℝ≥0∞) * X.ν B) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
    simpa only [N, B] using
      (avram_p2_e_compensator_original_grid_pair_rate_sum_exact
        X k s t hst n)
  calc
    (∫⁻ ω, (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)) ∂P)
        = ∫⁻ ω, ∑ i : Fin k, N 0 (s i) ω * N (s i) (t i) ω ∂P := by
            exact lintegral_congr hPoint
    _ = _ := hExpected
