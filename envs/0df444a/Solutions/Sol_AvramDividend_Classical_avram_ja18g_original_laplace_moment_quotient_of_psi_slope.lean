-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_laplace_moment_quotient_of_psi_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:09:28.614252+00:00
-- url     : https://prove2.me/submissions/b7ef959e-f128-4ee0-8701-9e28d8dc8cc8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Transfer an exponent right derivative to the original-process moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (a : ℝ)
    (hψ : Filter.Tendsto (fun θ : ℝ => X.ψ θ / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds a)) :
    Filter.Tendsto
      (fun θ : ℝ =>
        ((∫ ω, Real.exp (θ * X.X t ω) ∂P) - 1) / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds ((t : ℝ) * a)) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  let y : ℝ → ℝ := fun θ => (t : ℝ) * X.ψ θ
  let g : ℝ → ℝ := fun θ => y θ / θ
  have hθ : Tendsto (fun θ : ℝ => θ) l (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hg : Tendsto g l (nhds ((t : ℝ) * a)) := by
    simpa [g, y, mul_div_assoc] using (tendsto_const_nhds.mul hψ)
  have hy0 : Tendsto y l (nhds 0) := by
    have hh := hθ.mul hg
    have he : ∀ᶠ θ in l, θ * g θ = y θ := by
      filter_upwards [self_mem_nhdsWithin] with θ hθpos
      change (0 : ℝ) < θ at hθpos
      dsimp [g]
      field_simp [ne_of_gt hθpos]
    simpa using hh.congr' he
  have hds : Tendsto
      (fun θ => dslope Real.exp 0 (y θ)) l (nhds 1) := by
    have hd : ContinuousAt (dslope Real.exp 0) 0 :=
      continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt
    have hh := hd.tendsto.comp hy0
    simpa [Function.comp_def, dslope_same, Real.deriv_exp] using hh
  have hfactor (θ : ℝ) :
      (Real.exp (y θ) - 1) / θ = dslope Real.exp 0 (y θ) * g θ := by
    by_cases hθzero : θ = 0
    · subst θ
      simp [g]
    · have hs := sub_smul_dslope Real.exp (0 : ℝ) (y θ)
      simp only [sub_zero, Real.exp_zero, smul_eq_mul] at hs
      calc
        (Real.exp (y θ) - 1) / θ =
            (y θ * dslope Real.exp 0 (y θ)) / θ := by rw [← hs]
        _ = dslope Real.exp 0 (y θ) * g θ := by
          dsimp [g]
          field_simp [hθzero]
  have hExp : Tendsto
      (fun θ => (Real.exp (y θ) - 1) / θ)
      l (nhds ((t : ℝ) * a)) := by
    have hprod : Tendsto
        (fun θ => dslope Real.exp 0 (y θ) * g θ)
        l (nhds ((t : ℝ) * a)) := by
      simpa only [one_mul] using hds.mul hg
    convert hprod using 1
    funext θ
    exact hfactor θ
  have hMoment (θ : ℝ) (hθpos : 0 < θ) :
      (∫ ω, Real.exp (θ * X.X t ω) ∂P) = Real.exp (y θ) := by
    have h := levy_transition_exponential_eigenfunction X t θ hθpos.le 0
    simpa [y, SpectrallyNegativeLevy.ψ] using h
  apply hExp.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθpos
  rw [hMoment θ hθpos]
