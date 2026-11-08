-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian13_original_masked_grid_L2_limit_zero_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:46:45.00956+00:00
-- url     : https://prove2.me/submissions/759e107f-59f2-45c1-a8da-76cff7e88963

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_original_masked_grid_L2_limit_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual terminal Gaussian grid limit inherits L² membership and mean
zero from its centred original physical-grid approximations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v : ℝ)
    (S : ℕ → Finset ι) (s t : ℕ → ι → ℝ≥0)
    (M : Ω → ℝ) (hMMeas : AEStronglyMeasurable M P) :
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
      MemLp M 2 P ∧ (∫ ω, M ω ∂P) = 0 := by
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
      MemLp M 2 P ∧ (∫ ω, M ω ∂P) = 0
  intro hQ2 hQzero hL2
  have hM2 : MemLp M 2 P :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) hQ2 M hMMeas hL2
  refine ⟨hM2, ?_⟩
  exact avram_ubv_gaussian13_original_masked_grid_L2_limit_mean_zero
    X hν x D hD w u v S s t M hM2 hQ2 hQzero hL2
