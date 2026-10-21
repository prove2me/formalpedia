-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_bounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:46:36.994288+00:00
-- url     : https://prove2.me/submissions/be13b880-9334-4698-9ddf-4fe441f7af8e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_ae_zero_standing_bv_C2
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_vcstar_nonzero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Pointwise q-harmonicity of the scale function below the optimal barrier in the
prescribed C2 branch, for a process of bounded variation.

The residual is identified almost everywhere from the vanishing of its weighted
Laplace transform, the almost-everywhere vanishing is upgraded to pointwise
vanishing by the C2 regularity of the scale function, and the convergence of
the compensated Levy generator jump integral follows from the same C2
regularity of the barrier value.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
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
    have hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 (cstar W).toReal)),
        X.generator W x - q * W x = 0 :=
      scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
        X hX q hq W hW (cstar W).toReal ha hcont hweighted
    have hC2 : ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) :=
      scaleFunction_contDiffOn_two_of_vcstar_nonzero W hvc hk
    have hharm : ∀ x ∈ Ioo 0 (cstar W).toReal,
        X.generator W x - q * W x = 0 :=
      scaleFunction_generator_eq_q_of_ae_zero_standing_bv_C2
        X hX hbv q W hW (cstar W).toReal hC2 hae
    intro x hx
    refine ⟨?_, hharm x hx⟩
    exact scaleFunction_generatorIntegrable_of_vcstar_contDiff_two_cstar
      X hX q hq W hW hc hvc hk x hx
