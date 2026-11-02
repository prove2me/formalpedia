-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_covariance_null_sequences
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:15:38.936244+00:00
-- url     : https://prove2.me/submissions/22907b1b-cb3e-4ed7-886d-3f1eb76e7e53

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_energy_slope_right

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Original rightCont stopped Gaussian cross covariance has variance h*sigma squared. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (θ η : ℕ → ℝ)
    (hθ : Filter.Tendsto θ atTop (𝓝[>] (0 : ℝ)))
    (hη : Filter.Tendsto η atTop (𝓝[>] (0 : ℝ))) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto (fun n : ℕ =>
      (∫ ω, Z (θ n) ω * Z (η n) ω ∂P))
      atTop (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
  dsimp only
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  change Filter.Tendsto (fun n : ℕ =>
    (∫ ω, Z (θ n) ω * Z (η n) ω ∂P))
    atTop (𝓝 ((h : ℝ) * X.σ ^ 2))
  let A : ℝ := (h : ℝ) * X.σ ^ 2
  have hθ0 : Filter.Tendsto θ atTop (𝓝 (0 : ℝ)) :=
    hθ.mono_right nhdsWithin_le_nhds
  have hη0 : Filter.Tendsto η atTop (𝓝 (0 : ℝ)) :=
    hη.mono_right nhdsWithin_le_nhds
  have hθpos : ∀ᶠ n : ℕ in atTop, 0 < θ n :=
    hθ.eventually self_mem_nhdsWithin
  have hηpos : ∀ᶠ n : ℕ in atTop, 0 < η n :=
    hη.eventually self_mem_nhdsWithin
  have hθη0 : Filter.Tendsto (fun n : ℕ => θ n * η n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hθ0.mul hη0
  have hθηpos : ∀ᶠ n : ℕ in atTop, 0 < θ n * η n := by
    filter_upwards [hθpos, hηpos] with n hn hm
    exact mul_pos hn hm
  have hθη : Filter.Tendsto (fun n : ℕ => θ n * η n)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hθη0, hθηpos⟩
  have hslope : Filter.Tendsto
      (fun n : ℕ =>
        (Real.exp (A * (θ n * η n)) - 1) / (θ n * η n))
      atTop (𝓝 A) :=
    (avram_wave5_03a_exp_energy_slope_right A).comp hθη
  have heq : (fun n : ℕ =>
      (∫ ω, Z (θ n) ω * Z (η n) ω ∂P)) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.exp (A * (θ n * η n)) - 1) / (θ n * η n)) := by
    filter_upwards [hθpos, hηpos] with n hn hm
    have hcross :=
      avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
        X hν τ hτ T hbounded h (θ n) (η n) (le_of_lt hn) (le_of_lt hm)
    simpa only [Z, A, mul_assoc] using hcross
  exact hslope.congr' heq.symm
