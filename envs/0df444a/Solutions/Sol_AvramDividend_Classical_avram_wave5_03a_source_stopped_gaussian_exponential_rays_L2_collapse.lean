-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_rays_L2_collapse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:10:37.637548+00:00
-- url     : https://prove2.me/submissions/476c0c89-0e18-4f8a-a31e-ab23940b1e33

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_energy_slope_right

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Original stopped Gaussian exponential quotients collapse in L2 along any positive ray. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (b : ℝ) (hb : 0 < b) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto (fun ε : ℝ =>
      (∫ ω, (Z (Real.sqrt ε) ω - Z (b * Real.sqrt ε) ω) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  dsimp only
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  change Filter.Tendsto (fun ε : ℝ =>
    (∫ ω, (Z (Real.sqrt ε) ω - Z (b * Real.sqrt ε) ω) ^ 2 ∂P))
    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
  let A : ℝ := (h : ℝ) * X.σ ^ 2
  let D : ℝ → ℝ := fun ε =>
    (Real.exp (A * ε) - 1) / ε +
    ((Real.exp ((A * b ^ 2) * ε) - 1) / ε) / b ^ 2 -
    2 * (((Real.exp ((A * b) * ε) - 1) / ε) / b)
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hlim1 := avram_wave5_03a_exp_energy_slope_right A
  have hlim2 := avram_wave5_03a_exp_energy_slope_right (A * b ^ 2)
  have hlim3 := avram_wave5_03a_exp_energy_slope_right (A * b)
  have hlim : Filter.Tendsto D (𝓝[>] (0 : ℝ))
      (𝓝 (A + (A * b ^ 2) / b ^ 2 - 2 * ((A * b) / b))) :=
    (hlim1.add (hlim2.div_const (b ^ 2))).sub
      ((hlim3.div_const b).const_mul 2)
  have hvalue : A + (A * b ^ 2) / b ^ 2 -
      2 * ((A * b) / b) = 0 := by
    field_simp [hb0]
    ring
  have hzero : Filter.Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [hvalue] using hlim
  have heq : (fun ε : ℝ =>
      (∫ ω, (Z (Real.sqrt ε) ω - Z (b * Real.sqrt ε) ω) ^ 2 ∂P))
        =ᶠ[𝓝[>] (0 : ℝ)] D := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have he0 : ε ≠ 0 := ne_of_gt hε
    have hsqrt : (Real.sqrt ε) ^ 2 = ε :=
      Real.sq_sqrt (le_of_lt hε)
    have hs0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
    have hbs0 : 0 ≤ b * Real.sqrt ε :=
      mul_nonneg (le_of_lt hb) hs0
    have hbsq : (b * Real.sqrt ε) ^ 2 = b ^ 2 * ε := by
      rw [mul_pow, hsqrt]
    have hbcross : Real.sqrt ε * (b * Real.sqrt ε) = b * ε := by
      calc
        _ = b * (Real.sqrt ε) ^ 2 := by ring
        _ = b * ε := by rw [hsqrt]
    have hdist :=
      avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
        X hν τ hτ T hbounded h (Real.sqrt ε) (b * Real.sqrt ε)
          hs0 hbs0
    dsimp only at hdist
    change (∫ ω,
      (Z (Real.sqrt ε) ω - Z (b * Real.sqrt ε) ω) ^ 2 ∂P) = D ε
    rw [hdist]
    rw [hsqrt, hbsq, hbcross]
    have hexp1 :
        Real.exp ((h : ℝ) * (X.σ ^ 2 * ε)) =
          Real.exp (A * ε) := by
      congr 1
      dsimp [A]
      ring
    have hexp2 :
        Real.exp ((h : ℝ) * (X.σ ^ 2 * (b ^ 2 * ε))) =
          Real.exp ((A * b ^ 2) * ε) := by
      congr 1
      dsimp [A]
      ring
    have hexp3 :
        Real.exp ((h : ℝ) * (X.σ ^ 2 * Real.sqrt ε *
          (b * Real.sqrt ε))) =
          Real.exp ((A * b) * ε) := by
      congr 1
      dsimp [A]
      calc
        _ = ((h : ℝ) * X.σ ^ 2 * b) * (Real.sqrt ε) ^ 2 := by ring
        _ = ((h : ℝ) * X.σ ^ 2 * b) * ε := by rw [hsqrt]
    rw [hexp1, hexp2, hexp3]
    dsimp only [D]
    field_simp [he0, hb0]
  exact hzero.congr' heq.symm
