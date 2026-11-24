-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.C.sec_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:21:23.337971+00:00
-- url     : https://prove2.me/submissions/0d13397e-5d66-4633-b886-0fd28e77bc9a

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MapOfRealMul
import Theorems.Thm_CompanionTheory_ThKR_LL_dil_apply
import Theorems.Thm_CompanionTheory_ThKR_LL_ph_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.C
namespace CompanionTheory.ThKR.Mp.C
theorem _root_.solution (s : Mat l) (hA : IsUnit (bl Sum.inl Sum.inl s)) (f : Sch l) :
    sec s f 0 = (((√|s.toBlocks₁₁.det|)⁻¹ : ℝ) : ℂ) *
      fou l (ph (-(Ring.inverse (bl Sum.inl Sum.inl s) * bl Sum.inl Sum.inr s)) (fouInv l f)) 0 := by
  simp only [sec, big, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ph_apply,
    dil_apply hA.ringInverse, map_zero, inner_zero_left, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    smul_eq_mul]
end CompanionTheory.ThKR.Mp.C
