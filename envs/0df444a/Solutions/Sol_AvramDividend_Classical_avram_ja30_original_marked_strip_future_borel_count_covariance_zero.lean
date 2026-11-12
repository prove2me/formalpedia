-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja30_original_marked_strip_future_borel_count_covariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:49:14.125482+00:00
-- url     : https://prove2.me/submissions/98a33861-348a-4446-998e-baaee9f12a39

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja25_original_marked_strip_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_negative_band_integral_adapted
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical past marked strip and future Borel count are orthogonal by the
original filtration and the source compensated-count martingale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (hnm : n ≤ m)
    (s t : ℝ≥0) (hst : s ≤ t)
    (cut : ℕ) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1)))) :
    let S : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : Ω → ℝ := fun ω =>
      (∫ p in (Ioc 0 s ×ˢ S), p.2 ∂NX ω) -
        (s : ℝ) * (∫ z in S, z ∂X.ν)
    let N : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => H ω * ((N ω).toReal - r)) P ∧
    (∫ ω, H ω * ((N ω).toReal - r) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let S : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let H : Ω → ℝ := fun ω =>
    (∫ p in (Ioc 0 s ×ˢ S), p.2 ∂NX ω) -
      (s : ℝ) * (∫ z in S, z ∂X.ν)
  let N : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s t ×ˢ B)
  let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => H ω * ((N ω).toReal - r)) P ∧
    (∫ ω, H ω * ((N ω).toReal - r) ∂P) = 0
  have hNeg : ∀ z ∈ S, z ≤ 0 := by
    intro z hz
    exact le_of_lt (lt_of_le_of_lt hz.2
      (neg_lt_zero.mpr (by positivity)))
  have hAdapt : Measurable[𝓕 s] H := by
    exact (avram_mix_gauss14_original_negative_band_integral_adapted
      X s S measurableSet_Ioc hNeg).sub_const _
  have hStrong : StronglyMeasurable[𝓕 s] H :=
    hAdapt.stronglyMeasurable
  have hSq : Integrable (fun ω => (H ω) ^ 2) P := by
    simpa only [H, NX, S] using
      (avram_ja25_original_marked_strip_square_integrable
        X hFinite n m hnm s)
  have hL2 : MemLp H 2 P :=
    (memLp_two_iff_integrable_sq
      ((hAdapt.mono (𝓕.le s) le_rfl).aestronglyMeasurable)).2 hSq
  have hSource :=
    avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
      X t cut s t hst le_rfl ε hε B hB hBand hCut
      H hStrong hL2
  change Integrable (fun ω => H ω * ((N ω).toReal - r)) P ∧
    (∫ ω, H ω * ((N ω).toReal - r) ∂P) = 0 at hSource
  exact hSource
