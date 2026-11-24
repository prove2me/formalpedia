-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.fou_mq_fouInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:40.865881+00:00
-- url     : https://prove2.me/submissions/319e6f75-0422-4aab-a5f5-e9923e5dac92

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho
import Theorems.Thm_CompanionTheory_ThKR_LL_fou_mul_fouInv
import Theorems.Thm_CompanionTheory_ThKR_LL_mq_apply
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inl
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inr
import Theorems.Thm_GlobalTheory_RealWeil_fourierInv_dRho_inl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution (B : Matrix l l ℝ) (f : Sch l) :
    fou l (mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) B)) (fouInv l f)) =
      (4 * π * I : ℂ)⁻¹ • ∑ j, ∑ k, (B j k : ℂ) • (∂_{(EuclideanSpace.single j 1 : Eu l)}
        (∂_{(EuclideanSpace.single k 1 : Eu l)} f)) := by
  have e : ∀ u : Sch l, fou l (fouInv l u) = u := fun u => by
    rw [← ContinuousLinearMap.mul_apply, fou_mul_fouInv, ContinuousLinearMap.one_apply]
  rw [← e (_ • _)]
  congr 1
  have h : ∀ j (u : Sch l), fouInv l (dRho (Pi.single (Sum.inl j) 1) u) = -dRho (Pi.single (Sum.inr j) 1) (fouInv l u) :=
    fourierInv_dRho_inl
  simp only [← dRho_single_inl, map_smul, map_sum, h, map_neg, neg_neg]
  ext x
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [mq_apply, SchwartzMap.smul_apply, SchwartzMap.sum_apply, dRho_single_inr, smul_eq_mul,
    ContinuousLinearMap.neg_apply, inner_neg_right, inner_toEuclideanCLM, dotProduct, mulVec, Finset.mul_sum]
  push_cast
  simp only [mul_neg, neg_mul, neg_neg, Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp
  ring
end CompanionTheory.ThKR.LL
