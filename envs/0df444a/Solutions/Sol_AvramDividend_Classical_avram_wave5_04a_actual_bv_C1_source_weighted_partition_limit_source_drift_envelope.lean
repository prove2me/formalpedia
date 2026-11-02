-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_C1_source_weighted_partition_limit_source_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:50:35.728317+00:00
-- url     : https://prove2.me/submissions/f0237969-40d1-4d3e-8e96-cdf94962270a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Any existing real limit of uniformly bounded weighted original BV
source residual sums over refining fixed-endpoint partitions inherits
the source-only drift-path variation envelope. No Ito-Meyer identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (s t : ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k)) (n : ℕ → ℕ)
        (hstart : ∀ k : ℕ, u k 0 = s)
        (hend : ∀ k : ℕ, u k (n k) = t)
        (a : ℕ → ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (ha : ∀ k i : ℕ, |a k i| ≤ M)
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          (Finset.range (n k)).sum (fun i =>
            a k i * (R (u k (i + 1)) - R (u k i)))) atTop (𝓝 L)),
        |L| ≤ M * (((t : ℝ) - (s : ℝ)) * X.drift -
          (X.X t ω - X.X s ω)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hbound⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro s t u hu n hstart hend a M hM ha L hlim
  have hboundk (k : ℕ) :
      |(Finset.range (n k)).sum (fun i =>
        a k i * (R (u k (i + 1)) - R (u k i)))| ≤
        M * (((t : ℝ) - (s : ℝ)) * X.drift -
          (X.X t ω - X.X s ω)) := by
    have hk := hbound (u k) (hu k) (n k) (a k) M hM (ha k)
    simpa [hstart k, hend k] using hk
  have habslim :
      Tendsto (fun k : ℕ =>
        |(Finset.range (n k)).sum (fun i =>
          a k i * (R (u k (i + 1)) - R (u k i)))|) atTop (𝓝 |L|) :=
    (continuous_abs.tendsto L).comp hlim
  apply le_of_tendsto habslim
  exact Filter.Eventually.of_forall hboundk
