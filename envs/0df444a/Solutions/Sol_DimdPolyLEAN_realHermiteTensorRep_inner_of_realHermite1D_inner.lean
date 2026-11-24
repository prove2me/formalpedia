-- Prove2me | solution 1 for DimdPolyLEAN.realHermiteTensorRep_inner_of_realHermite1D_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:31.817596+00:00
-- url     : https://prove2.me/submissions/7dec3f4d-3609-412b-ba1e-4ac6c2e97dd9

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
theorem _root_.solution
    {d : Nat} (alpha beta : Idx d)
    (hinner1 : ∀ n m : Nat,
      (∫ t : ℝ, realHermite1D m t * star (realHermite1D n t)) =
        if n = m then (1 : ℂ) else 0) :
    (∫ x : RealVec d,
      realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x)) =
      if alpha = beta then (1 : ℂ) else 0 := by
  calc
    (∫ x : RealVec d,
      realHermiteTensorRep beta x * star (realHermiteTensorRep alpha x))
        =
          ∫ x : RealVec d,
            (fun y : Fin d -> ℝ =>
              ∏ q : Fin d, realHermite1D (beta q) (y q) *
                star (realHermite1D (alpha q) (y q))) (WithLp.ofLp x) := by
          congr with x
          simp [realHermiteTensorRep, Finset.prod_mul_distrib]
    _ =
        ∫ y : Fin d -> ℝ,
          ∏ q : Fin d, realHermite1D (beta q) (y q) *
            star (realHermite1D (alpha q) (y q)) := by
          simpa [MeasurableEquiv.coe_toLp_symm] using
            (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
              (g := fun y : Fin d -> ℝ =>
                ∏ q : Fin d, realHermite1D (beta q) (y q) *
                  star (realHermite1D (alpha q) (y q)))
    _ = if alpha = beta then (1 : ℂ) else 0 := by
      have hprod :
          (∫ y : Fin d -> ℝ,
            ∏ q : Fin d, realHermite1D (beta q) (y q) *
              star (realHermite1D (alpha q) (y q))) =
            ∏ q : Fin d,
              ∫ t : ℝ, realHermite1D (beta q) t *
                star (realHermite1D (alpha q) t) := by
        exact
          MeasureTheory.integral_fintype_prod_volume_eq_prod
            (f := fun q (t : ℝ) =>
              realHermite1D (beta q) t * star (realHermite1D (alpha q) t))
      rw [hprod]
      simp_rw [hinner1]
      by_cases h : alpha = beta
      · simp_all only [RCLike.star_def, ↓reduceIte, Finset.prod_const_one]
      · rw [if_neg h]
        have hq : ∃ q, alpha q ≠ beta q := by
          by_contra hnone
          apply h
          funext q
          simp_all only [RCLike.star_def, ne_eq, not_exists, Decidable.not_not]
        rcases hq with ⟨q, hq⟩
        have hfactor : (if alpha q = beta q then (1 : ℂ) else 0) = 0 := by simp [hq]
        rw [show (∏ q : Fin d, if alpha q = beta q then (1 : ℂ) else 0) = 0 from by
          rw [Finset.prod_eq_zero_iff]
          exact ⟨q, Finset.mem_univ q, hfactor⟩]
end DimdPolyLEAN
