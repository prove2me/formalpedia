-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_grid_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:48:06.935048+00:00
-- url     : https://prove2.me/submissions/eed98dbd-f508-4a3a-b9a9-75d2b3621841

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original marked-jump finite-grid quadratic budget follows
from all physical diagonal moments and disjoint-cell cross moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (B : ι → Set ℝ) (J : ι → Ω → ℝ)
    (hSource : ∀ i ∈ S, ∀ ω, J i ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)).toReal)
    (r c : ι → ℝ)
    (hRate : ∀ i ∈ S, r i =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal)
    (hPairInt : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun ω =>
      (c i * (J i ω - r i)) * (c j * (J j ω - r j))) P)
    (hPairMoment : ∀ i ∈ S, ∀ j ∈ S,
      (∫ ω, (c i * (J i ω - r i)) *
        (c j * (J j ω - r j)) ∂P) =
          if i = j then c i ^ 2 * r i else 0) :
    (∫ ω, (∑ i ∈ S, c i * (J i ω - r i)) ^ 2 ∂P) =
      ∑ i ∈ S, c i ^ 2 * r i := by
  let f : ι → Ω → ℝ := fun i ω => c i * (J i ω - r i)
  have hPair : ∀ i ∈ S, ∀ j ∈ S,
      Integrable (fun ω => f i ω * f j ω) P := hPairInt
  have hInner (i : ι) (hi : i ∈ S) :
      Integrable (fun ω => ∑ j ∈ S, f i ω * f j ω) P := by
    exact integrable_finset_sum S (fun j hj => hPair i hi j hj)
  have hOuter : Integrable (fun ω =>
      ∑ i ∈ S, ∑ j ∈ S, f i ω * f j ω) P := by
    exact integrable_finset_sum S hInner
  calc
    _ = ∫ ω, ∑ i ∈ S, ∑ j ∈ S, f i ω * f j ω ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      change (∑ i ∈ S, f i ω) ^ 2 =
        ∑ i ∈ S, ∑ j ∈ S, f i ω * f j ω
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i ∈ S, ∑ j ∈ S,
        (∫ ω, f i ω * f j ω ∂P) := by
      rw [integral_finset_sum S hInner]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finset_sum S (fun j hj => hPair i hi j hj)]
    _ = ∑ i ∈ S, c i ^ 2 * r i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hm : ∀ j ∈ S,
          (∫ ω, f i ω * f j ω ∂P) =
            if i = j then c i ^ 2 * r i else 0 :=
        hPairMoment i hi
      calc
        _ = ∑ j ∈ S, if i = j then c i ^ 2 * r i else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hm j hj
        _ = c i ^ 2 * r i := by simp [hi]
