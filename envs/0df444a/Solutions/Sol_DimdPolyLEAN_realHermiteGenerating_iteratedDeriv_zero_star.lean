-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteGenerating_iteratedDeriv_zero_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:27.066922+00:00
-- url     : https://prove2.me/submissions/3a3e0ef3-80fb-400c-b54a-cd4adfd84709

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
public import Theorems.Thm_DimdPolyLEAN_realHermiteGenerating_conj
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
private lemma star_deriv_of_conj_symm {g : ℂ → ℂ}
    (hgdiff : Differentiable ℂ g)
    (hgstar : ∀ z : ℂ, star (g z) = g (star z)) (z : ℂ) :
    star (deriv g z) = deriv g (star z) := by
  have hderiv := (hgdiff z).hasDerivAt.conj_conj
  have hfun : (conj ∘ g ∘ conj) = g := by
    funext x
    simp_all only [RCLike.star_def, hasDerivAt_conj_conj_iff, RingHomCompTriple.comp_apply,
      RingHom.id_apply, hasDerivAt_deriv_iff, Function.comp_apply]
  have hderiv' : HasDerivAt g (star (deriv g z)) (star z) := by simpa [hfun] using hderiv
  exact hderiv'.deriv.symm
private lemma star_iteratedDeriv_of_conj_symm {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : WithTop ℕ∞) f)
    (hfstar : ∀ z : ℂ, star (f z) = f (star z)) :
    ∀ n : ℕ, ∀ z : ℂ,
      star (iteratedDeriv n f z) = iteratedDeriv n f (star z) := by
  intro n
  induction n with
  | zero =>
      simp_all only [RCLike.star_def, iteratedDeriv_zero, implies_true]
  | succ n ih =>
      intro z
      simp only [iteratedDeriv_succ]
      exact star_deriv_of_conj_symm
        (g := iteratedDeriv n f)
        (hf.differentiable_iteratedDeriv n (by simp))
        ih
        z
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
theorem _root_.solution (n : ℕ) (t : ℝ) :
    star (iteratedDeriv n (realHermiteGenerating t) 0) =
      iteratedDeriv n (realHermiteGenerating t) 0 := by
  have hcont : ContDiff ℂ (⊤ : WithTop ℕ∞) (realHermiteGenerating t) := by
    unfold realHermiteGenerating
    fun_prop
  have h := star_iteratedDeriv_of_conj_symm
    (f := realHermiteGenerating t) hcont
    (fun z => realHermiteGenerating_conj t z) n 0
  simpa using h
end DimdPolyLEAN
