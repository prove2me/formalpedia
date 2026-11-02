-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_original_stopped_gaussian_quotient_two_sequence_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:05:45.00146+00:00
-- url     : https://prove2.me/submissions/88a1587d-666a-4aec-83d5-e5db52eb8347

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_energy_slope_right

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Genuine source L2 Cauchy distance for any two positive null sequences. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (θ η : ℕ → ℝ)
    (hθ : Filter.Tendsto θ atTop (𝓝[>] (0 : ℝ)))
    (hη : Filter.Tendsto η atTop (𝓝[>] (0 : ℝ))) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto (fun n : ℕ =>
      (∫ ω, (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P))
      atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  change Filter.Tendsto (fun n : ℕ =>
    (∫ ω, (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P))
    atTop (𝓝 (0 : ℝ))
  let A : ℝ := (h : ℝ) * X.σ ^ 2
  have hθ0 : Filter.Tendsto θ atTop (𝓝 (0 : ℝ)) :=
    hθ.mono_right nhdsWithin_le_nhds
  have hη0 : Filter.Tendsto η atTop (𝓝 (0 : ℝ)) :=
    hη.mono_right nhdsWithin_le_nhds
  have hθpos : ∀ᶠ n : ℕ in atTop, 0 < θ n :=
    hθ.eventually self_mem_nhdsWithin
  have hηpos : ∀ᶠ n : ℕ in atTop, 0 < η n :=
    hη.eventually self_mem_nhdsWithin
  have hθsq0 : Filter.Tendsto (fun n : ℕ => (θ n) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_two, zero_mul] using hθ0.mul hθ0
  have hηsq0 : Filter.Tendsto (fun n : ℕ => (η n) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_two, zero_mul] using hη0.mul hη0
  have hθη0 : Filter.Tendsto (fun n : ℕ => θ n * η n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hθ0.mul hη0
  have hθsqpos : ∀ᶠ n : ℕ in atTop, 0 < (θ n) ^ 2 := by
    filter_upwards [hθpos] with n hn
    exact sq_pos_of_pos hn
  have hηsqpos : ∀ᶠ n : ℕ in atTop, 0 < (η n) ^ 2 := by
    filter_upwards [hηpos] with n hn
    exact sq_pos_of_pos hn
  have hθηpos : ∀ᶠ n : ℕ in atTop, 0 < θ n * η n := by
    filter_upwards [hθpos, hηpos] with n hn hm
    exact mul_pos hn hm
  have hθsq : Filter.Tendsto (fun n : ℕ => (θ n) ^ 2)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hθsq0, hθsqpos⟩
  have hηsq : Filter.Tendsto (fun n : ℕ => (η n) ^ 2)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hηsq0, hηsqpos⟩
  have hθη : Filter.Tendsto (fun n : ℕ => θ n * η n)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hθη0, hθηpos⟩
  have h1 : Filter.Tendsto
      (fun n : ℕ => (Real.exp (A * (θ n) ^ 2) - 1) / (θ n) ^ 2)
      atTop (𝓝 A) :=
    (avram_wave5_03a_exp_energy_slope_right A).comp hθsq
  have h2 : Filter.Tendsto
      (fun n : ℕ => (Real.exp (A * (η n) ^ 2) - 1) / (η n) ^ 2)
      atTop (𝓝 A) :=
    (avram_wave5_03a_exp_energy_slope_right A).comp hηsq
  have h3 : Filter.Tendsto
      (fun n : ℕ => (Real.exp (A * (θ n * η n)) - 1) / (θ n * η n))
      atTop (𝓝 A) :=
    (avram_wave5_03a_exp_energy_slope_right A).comp hθη
  have hlim : Filter.Tendsto (fun n : ℕ =>
      (Real.exp (A * (θ n) ^ 2) - 1) / (θ n) ^ 2 +
      (Real.exp (A * (η n) ^ 2) - 1) / (η n) ^ 2 -
      2 * ((Real.exp (A * (θ n * η n)) - 1) / (θ n * η n)))
      atTop (𝓝 (0 : ℝ)) := by
    have hcalc := (h1.add h2).sub (h3.const_mul 2)
    have hval : A + A - 2 * A = 0 := by ring
    simpa only [hval] using hcalc
  have heq : (fun n : ℕ =>
      (∫ ω, (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P)) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.exp (A * (θ n) ^ 2) - 1) / (θ n) ^ 2 +
        (Real.exp (A * (η n) ^ 2) - 1) / (η n) ^ 2 -
        2 * ((Real.exp (A * (θ n * η n)) - 1) / (θ n * η n))) := by
    filter_upwards [hθpos, hηpos] with n hn hm
    have hdist :=
      avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
        X hν τ hτ T hbounded h (θ n) (η n) (le_of_lt hn) (le_of_lt hm)
    dsimp only at hdist
    simpa only [A, Z, mul_assoc] using hdist
  exact hlim.congr' heq.symm
