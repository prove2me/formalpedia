-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:17.310877+00:00
-- url     : https://prove2.me/submissions/1bdf2957-fa36-47ce-950e-2df89daa655c

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution (t : ℝ) (u : ℂ) :
    star (realHermiteGenerating t u) = realHermiteGenerating t (star u) := by
  unfold realHermiteGenerating
  rw [star_mul]
  have hpi : star (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) =
      (((Real.pi ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) := by
    simp_all only [one_div, RCLike.star_def, Complex.conj_ofReal]
  rw [hpi, mul_comm]
  congr 1
  change (starRingEnd ℂ)
      (Complex.exp (-(↑t ^ 2 / 2) + ↑√2 * ↑t * u - u ^ 2 / 2)) =
    Complex.exp (-(↑t ^ 2 / 2) + ↑√2 * ↑t * star u - star u ^ 2 / 2)
  rw [← Complex.exp_conj]
  congr 1
  have htwo : (starRingEnd ℂ) 2 = (2 : ℂ) := Complex.conj_ofReal 2
  simp_all only [one_div, RCLike.star_def, Complex.conj_ofReal, map_sub, map_add, map_neg, map_div₀,
    map_pow, map_mul]
end DimdPolyLEAN
