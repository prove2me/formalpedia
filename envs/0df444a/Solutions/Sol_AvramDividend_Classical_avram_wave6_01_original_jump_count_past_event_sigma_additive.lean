-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_jump_count_past_event_sigma_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:04:11.111644+00:00
-- url     : https://prove2.me/submissions/9b1dfd4c-1017-45fe-b9ff-178b64957b2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_jump_count_is_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : Set (ℝ≥0 × ℝ)) (hC : MeasurableSet C)
    (A : ℕ → Set Ω) (hAm : ∀ n, MeasurableSet (A n))
    (hAd : Pairwise (Function.onFun Disjoint A)) :
    (∫⁻ ω in ⋃ n, A n, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) =
      ∑' n, (∫⁻ ω in A n, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := by
  classical
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_event_weighted_jump_count_is_measure X C hC
  have hU : MeasurableSet (⋃ n, A n) :=
    MeasurableSet.iUnion hAm
  calc
    (∫⁻ ω in ⋃ n, A n, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) =
        Q (⋃ n, A n) := (hQ _ hU).symm
    _ = ∑' n, Q (A n) := measure_iUnion hAd hAm
    _ = ∑' n, (∫⁻ ω in A n, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := by
      exact tsum_congr (fun n => hQ (A n) (hAm n))
