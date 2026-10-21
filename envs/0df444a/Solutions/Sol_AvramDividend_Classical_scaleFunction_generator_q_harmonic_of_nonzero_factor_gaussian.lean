-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:02:12.418535+00:00
-- url     : https://prove2.me/submissions/fef9039f-7390-4cc1-b71a-bad23fd2d2b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two
import Theorems.Thm_AvramDividend_Classical_scaledW_contDiffOn_two_of_W_contDiffOn_two_positive
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
Pointwise q-harmonicity of the scale function below the optimal barrier in the
Gaussian branch, without the extra hypothesis on the small jumps.

This is the Gaussian branch of the core analytic obligation of Lemma 4 of
Avram.  The proof composes five Proved results, and the argument is the same
as the one of the sibling theorem
`scaleFunction_generator_q_harmonic_of_nonzero_factor_gaussian_of_finite_small_jump_measure`,
which carries the additional hypothesis `X.ν (Iic (-1 : ℝ)) ≠ ⊤`.  That
hypothesis is never used: the Gaussian origin condition `W 0 = 0` follows
from `0 < X.σ` alone, by
`scaleFunction_zero_origin_gaussian_without_standing`, so the whole argument
goes through without it.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hc : 0 < cstar W)
    (hC2 : ContDiffOn ℝ 2 W (Ioi 0))
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
    -- The residual is identified almost everywhere on `(0, c*)` from the
    -- vanishing of its weighted Laplace transform.
    have hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 (cstar W).toReal)),
        X.generator W x - q * W x = 0 :=
      scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
        X hX q hq W hW (cstar W).toReal ha hcont hweighted
    -- The `C²` regularity of the scale function on the positive half-line
    -- restricts to the interval below the barrier level.
    have hC2' : ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) :=
      hC2.mono (fun x hx => hx.1)
    -- Below the barrier level the barrier value is the normalised scale
    -- function, so the smoothness of the scale function is the smoothness of
    -- the barrier value.
    have hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal) := by
      have hscaled : ContDiffOn ℝ 2
          (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal))
          (Ioo 0 (cstar W).toReal) :=
        scaledW_contDiffOn_two_of_W_contDiffOn_two_positive W
          (cstar W).toReal ha (Ioo 0 (cstar W).toReal) hC2'
      have hsupport : ∀ z : ℝ, z < 0 → W z = 0 := by
        intro z hz
        exact hW.1 z hz
      refine hscaled.congr ?_
      intro z hz
      exact vcstar_eq_scaledW_le_cstar_of_support W hsupport z (le_of_lt hz.2)
    -- The Gaussian origin condition `W 0 = 0` needs only `0 < X.σ`.
    have hzero : W 0 = 0 :=
      scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
    -- The almost-everywhere vanishing is upgraded to pointwise vanishing.
    have hharm : ∀ x ∈ Ioo 0 (cstar W).toReal,
        X.generator W x - q * W x = 0 :=
      scaleFunction_generator_eq_q_of_ae_harmonic_C2_nonzero
        X hX q hq W hW hc hk hvc (Or.inl hzero) hae
    intro x hx
    refine ⟨?_, hharm x hx⟩
    exact scaleFunction_generatorIntegrable_of_contDiff_two
      X q W hW (cstar W).toReal x hx hC2'
