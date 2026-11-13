-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja36_original_negative_borel_cell_factorial_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:58:04.588857+00:00
-- url     : https://prove2.me/submissions/737db688-c28c-43c0-b18c-2e18edfb6ddc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_factorial_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_real_count_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_poisson_law
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_count_second_moment_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Nat
noncomputable section

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
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let J : Ω → ℝ := fun ω => (N ω).toReal
  let r0 : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => J ω * (J ω - 1)) P ∧
    (∫ ω, J ω * (J ω - 1) ∂P) = r0 ^ 2
  have hFactorI : Integrable (fun ω => J ω * (J ω - 1)) P := by
    simpa only [N, J] using
      (avram_a20_original_negative_borel_factorial_integrable
        X hFinite T B hB hNeg)
  have hJ2I : Integrable (fun ω => J ω ^ 2) P := by
    simpa only [N, J] using
      (avram_a20_original_negative_borel_real_count_square_integrable
        X hFinite T B hB hNeg)
  obtain ⟨K, r, hKm, hKlaw, hKJ, hR⟩ :=
    (avram_a20_original_negative_borel_count_poisson_law
      X hFinite T B hB hNeg)
  have hSecond : (∫ ω, (J ω) ^ 2 ∂P) =
      (r : ℝ) ^ 2 + (r : ℝ) := by
    calc
      (∫ ω, J ω ^ 2 ∂P) =
          (∫ ω, (K ω : ℝ) ^ 2 ∂P) := by
        apply integral_congr_ae
        filter_upwards [hKJ] with ω hω
        exact congrArg (fun x : ℝ => x ^ 2) hω.symm
      _ = _ :=
        (avram_wave4_p1_poisson_count_second_moment_integrable
          P K hKm r hKlaw).2
  obtain ⟨hJI, hFirst⟩ :=
    (avram_ja35_original_negative_borel_real_count_first_moment
      X hFinite T B hB hNeg)
  have hFirst' : (∫ ω, J ω ∂P) = r0 := by
    simpa only [N, J, r0] using hFirst
  have hId : (fun ω => J ω * (J ω - 1)) =
      (fun ω => J ω ^ 2 - J ω) := by
    funext ω
    ring
  refine ⟨hFactorI, ?_⟩
  rw [hId, integral_sub hJ2I hJI, hSecond, hFirst']
  change (r : ℝ) ^ 2 + (r : ℝ) - r0 = r0 ^ 2
  rw [hR]
  ring
