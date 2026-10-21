-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:31:30.759154+00:00
-- url     : https://prove2.me/submissions/310c7499-52e5-41bb-b4d3-c99fe9e41d68

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Pointwise q-harmonicity of the scale function below the optimal barrier in the
prescribed C2 branch.

The residual is identified almost everywhere from the vanishing of its weighted
Laplace transform, the almost-everywhere vanishing is upgraded to pointwise
vanishing by the continuity of the residual, and the convergence of the
compensated Levy generator jump integral follows from the C2 regularity of the
barrier value.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hbranch : W 0 = 0 ∨ X.BoundedVariation)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by
  -- The barrier level may be infinite; in that case `(cstar W).toReal = 0` and
  -- the interval `(0, (cstar W).toReal)` is empty, so the conclusion is
  -- vacuous.  The hypotheses do not exclude `cstar W = ⊤`.
  by_cases htop : cstar W = ⊤
  · intro x hx
    have htop_toReal : (cstar W).toReal = 0 := by
      rw [htop]
      exact ENNReal.toReal_top
    have hx' : x ∈ Ioo (0 : ℝ) 0 := by
      have hx' := hx
      rw [htop_toReal] at hx'
      exact hx'
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hx'
    exact (lt_irrefl 0 (h1.trans h2)).elim
  · have hne_zero : cstar W ≠ 0 := ne_of_gt hc
    have ha : 0 < (cstar W).toReal := ENNReal.toReal_pos hne_zero htop
    have hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 (cstar W).toReal)),
        X.generator W x - q * W x = 0 :=
      scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
        X hX q hq W hW (cstar W).toReal ha hcont hweighted
    have hharm : ∀ x ∈ Ioo 0 (cstar W).toReal,
        X.generator W x - q * W x = 0 :=
      scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero
        X hX q hq W hW hc hk hvc hbranch hae
    intro x hx
    refine ⟨?_, hharm x hx⟩
    exact scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar
      X hX q hq W hW hc hvc hk x hx
