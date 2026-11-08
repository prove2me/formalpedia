-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian13_original_masked_grid_L2_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:30:13.613554+00:00
-- url     : https://prove2.me/submissions/49de52c9-7a38-4182-8fc4-28bde879d661

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- L² convergence of the original masked Gaussian physical-grid sums preserves
their genuine mean-zero property, without a pathwise dominating envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v : ℝ)
    (S : ℕ → Finset ι) (s t : ℕ → ι → ℝ≥0)
    (M : Ω → ℝ) (hM2 : MemLp M 2 P) :
    let G : ℝ≥0 → Ω → ℝ := fun r ω =>
      let y := Function.leftLim
        (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
      X.σ * if y ∈ Icc u v then deriv w y else 0
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G (s n i) ω *
        (X.X (t n i) ω - X.X (s n i) ω -
          ((t n i - s n i) : ℝ) * X.c)
    (∀ n, MemLp (Q n) 2 P) →
    (∀ n, (∫ ω, Q n ω ∂P) = 0) →
    Tendsto (fun n => eLpNorm (Q n - M) 2 P) atTop (𝓝 0) →
      (∫ ω, M ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let G : ℝ≥0 → Ω → ℝ := fun r ω =>
    let y := Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    X.σ * if y ∈ Icc u v then deriv w y else 0
  let Q : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n, G (s n i) ω *
      (X.X (t n i) ω - X.X (s n i) ω -
        ((t n i - s n i) : ℝ) * X.c)
  change (∀ n, MemLp (Q n) 2 P) →
    (∀ n, (∫ ω, Q n ω ∂P) = 0) →
    Tendsto (fun n => eLpNorm (Q n - M) 2 P) atTop (𝓝 0) →
      (∫ ω, M ω ∂P) = 0
  intro hQ2 hQzero hL2
  have hL1bound (n : ℕ) :
      eLpNorm (Q n - M) 1 P ≤ eLpNorm (Q n - M) 2 P :=
    eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((hQ2 n).aestronglyMeasurable.sub hM2.aestronglyMeasurable)
  have hL1 :
      Tendsto (fun n => eLpNorm (Q n - M) 1 P) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL2
      (fun n => zero_le) hL1bound
  have hInt := tendsto_integral_of_L1' M hM2.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun n => (hQ2 n).integrable (by norm_num))) hL1
  exact tendsto_nhds_unique hInt (by
    simpa only [hQzero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
