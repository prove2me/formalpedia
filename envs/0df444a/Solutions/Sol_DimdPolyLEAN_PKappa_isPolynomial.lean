-- Prove2me | solution 1 for DimdPolyLEAN.PKappa_isPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:37.775277+00:00
-- url     : https://prove2.me/submissions/ada14cf2-b726-4a09-b829-af13842340d8

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


section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
private theorem tKappaCoordPoly_eval
    {d : Nat} (_kappa : MultiIndex d) (ξ : PhaseSpace d) (q : Fin d) :
    MvPolynomial.eval (phaseSpacePolyEval ξ) (tKappaCoordPoly q) =
      TKappa ξ q := by
  simp [tKappaCoordPoly, TKappa, phaseSpacePolyEval, div_eq_mul_inv]
  ring
private theorem tKappaConjCoordPoly_eval
    {d : Nat} (_kappa : MultiIndex d) (ξ : PhaseSpace d) (q : Fin d) :
    MvPolynomial.eval (phaseSpacePolyEval ξ) (tKappaConjCoordPoly q) =
      star (TKappa ξ q) := by
  simp [tKappaConjCoordPoly, TKappa, phaseSpacePolyEval, div_eq_mul_inv]
  ring
private theorem complexHermiteMvPolynomial_eval
    {σ : Type*} (ev : σ -> ℂ)
    (m n : Nat) (Z Zstar : MvPolynomial σ ℂ) (z : ℂ)
    (hZ : MvPolynomial.eval ev Z = z)
    (hZstar : MvPolynomial.eval ev Zstar = star z) :
    MvPolynomial.eval ev (complexHermiteMvPolynomial m n Z Zstar) =
      complexHermite m n z := by
  simp [complexHermiteMvPolynomial, complexHermite, hZ, hZstar, mul_assoc]
private theorem phi1DMvPolynomial_eval
    {σ : Type*} (ev : σ -> ℂ)
    (k n : Nat) (Z Zstar : MvPolynomial σ ℂ) (z : ℂ)
    (hZ : MvPolynomial.eval ev Z = z)
    (hZstar : MvPolynomial.eval ev Zstar = star z) :
    MvPolynomial.eval ev (phi1DMvPolynomial k n Z Zstar) = phi1D k n z := by
  simp [phi1DMvPolynomial, phi1D,
    complexHermiteMvPolynomial_eval ev n k Z Zstar z hZ hZstar]
private theorem PhiTKappaMvPolynomial_eval
    {d : Nat} (kappa alpha : MultiIndex d) (ξ : PhaseSpace d) :
    MvPolynomial.eval (phaseSpacePolyEval ξ) (PhiTKappaMvPolynomial kappa alpha) =
      Phi kappa alpha (TKappa ξ) := by
  simp only [PhiTKappaMvPolynomial, Phi, MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro q _hq
  exact phi1DMvPolynomial_eval (phaseSpacePolyEval ξ) (kappa q) (alpha q)
    (tKappaCoordPoly q) (tKappaConjCoordPoly q) (TKappa ξ q)
    (tKappaCoordPoly_eval kappa ξ q) (tKappaConjCoordPoly_eval kappa ξ q)
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    IsPhaseSpacePolynomial (PKappa kappa) := by
  let _ := hd
  refine ⟨MvPolynomial.C
      ((-1 : ℂ) ^ ((Finset.univ : Finset (Fin d)).sum fun q => kappa q)) *
    PhiTKappaMvPolynomial kappa kappa, ?_⟩
  intro ξ
  simp [PKappa, PhiTKappaMvPolynomial_eval]
end DimdPolyLEAN
