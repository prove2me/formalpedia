-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.column_operation_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:43:56.8294+00:00
-- url     : https://prove2.me/submissions/bfb4011a-92a5-4e28-ba65-48ddb32b4544

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_row
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x2 Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.ColOp := by
  intro K _ n Z u m c r hZ hu hrc hξ
  have hU := colOp_mul Z m c hZ
  set ξ := Z⁻¹ *ᵥ m with hξd
  refine ⟨⟨?_, ?_⟩, hU, ?_, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    by_cases hb : b = c
    · subst hb; simp [vecMulVec_apply, hξ a hab'.le, hab'.ne']
    · simp [vecMulVec_apply, hb, hab'.ne']
  · intro a
    by_cases ha : a = c
    · subst ha; simp [vecMulVec_apply, hξ a le_rfl]
    · simp [vecMulVec_apply, ha]
  · intro a b hca
    rw [colOp_row Z m c hZ (hξ c le_rfl), ← hξd, hξ a hca, zero_mul, sub_zero]
  · have e1 : u * (1 + vecMulVec ξ (Pi.single c 1)) = u + vecMulVec (u *ᵥ ξ) (Pi.single c 1) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec]
    have e2 : (u *ᵥ ξ) r = ξ r := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single r]
      · simp [hu.2 r]
      · intro b _ hb
        rcases lt_or_gt_of_ne hb with h | h
        · have : u r b = 0 := hu.1 (by simpa using h)
          simp [this]
        · have : c ≤ b := by rw [Fin.le_def]; have := Fin.lt_def.1 h; omega
          simp [hξ b this]
      · simp
    rw [e1]
    unfold sUp
    have : ∀ j : Fin n, (if h : j.val + 1 < n then
        (u + vecMulVec (u *ᵥ ξ) (Pi.single c 1)) j ⟨j.val + 1, h⟩ else 0) =
        (if h : j.val + 1 < n then u j ⟨j.val + 1, h⟩ else 0) + (if j = r then ξ r else 0) := by
      intro j
      by_cases h : j.val + 1 < n
      · by_cases hj : j = r
        · subst hj
          have : (⟨j.val + 1, h⟩ : Fin n) = c := Fin.ext hrc
          simp [h, vecMulVec_apply, this, e2]
        · have : (⟨j.val + 1, h⟩ : Fin n) ≠ c := fun hh => hj (Fin.ext (by
            have := congrArg Fin.val hh; simp at this; omega))
          simp [h, vecMulVec_apply, this, hj]
      · have hj : j ≠ r := fun hh => h (by rw [hh, hrc]; exact c.2)
        simp [h, hj]
    simp only [this, Finset.sum_add_distrib]
    simp
end Formalism.FourierDecayAlt.P
