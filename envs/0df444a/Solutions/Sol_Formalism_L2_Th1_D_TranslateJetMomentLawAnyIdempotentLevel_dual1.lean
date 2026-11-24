-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.dual1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:51.679592+00:00
-- url     : https://prove2.me/submissions/5a1eed3f-bb64-4645-b047-4bd99d56f35e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_sum_odd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
variable {ι : Type}
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution [Fintype ι] [DecidableEq ι] (hd : Even d) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (hT : TrDual d σ om oms)
    (x y : Bool × ι) :
    (∑ s : ZMod d, pXY σ om oms x s * mXY σ om oms s y) = if x = y then 1 else 0 := by
  have hit : ∀ (n : ℕ) (a b : K), σ^[n] (a * b) = σ^[n] a * σ^[n] b := by
    intro n
    induction n with
    | zero => intro a b; rfl
    | succ n ih =>
      intro a b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        map_mul]
  obtain ⟨-, hT⟩ := hT
  obtain ⟨bx, r⟩ := x
  obtain ⟨bY, r'⟩ := y
  cases bx <;> cases bY
  · calc (∑ s : ZMod d, pXY σ om oms (false, r) s * mXY σ om oms s (false, r'))
          = ∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (om r' * oms r) else 0 := by
            refine Finset.sum_congr rfl fun s _ => ?_
            by_cases h : s.val % 2 = 0 <;> simp [pXY, mXY, h, hit, mul_comm]
      _ = _ := by
            rw [hT r' r]
            by_cases hr : r = r'
            · subst hr; simp
            · simp [hr, Ne.symm hr]
  · have h0 : ∀ s : ZMod d, pXY σ om oms (false, r) s * mXY σ om oms s (true, r') = 0 := by
      intro s
      by_cases h : s.val % 2 = 0 <;> simp [pXY, mXY, h]
    simp [h0]
  · have h0 : ∀ s : ZMod d, pXY σ om oms (true, r) s * mXY σ om oms s (false, r') = 0 := by
      intro s
      by_cases h : s.val % 2 = 0 <;> simp [pXY, mXY, h]
    simp [h0]
  · calc (∑ s : ZMod d, pXY σ om oms (true, r) s * mXY σ om oms s (true, r'))
          = ∑ s : ZMod d, if s.val % 2 = 0 then 0 else σ^[s.val] (om r * oms r') := by
            refine Finset.sum_congr rfl fun s _ => ?_
            by_cases h : s.val % 2 = 0 <;> simp [pXY, mXY, h, hit]
      _ = _ := by
            rw [sum_odd hd σ (c := om r * oms r') (by rw [hit, (hfix r).1, (hfix r').2]), hT r r']
            by_cases hr : r = r'
            · subst hr; simp
            · simp [hr]
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
