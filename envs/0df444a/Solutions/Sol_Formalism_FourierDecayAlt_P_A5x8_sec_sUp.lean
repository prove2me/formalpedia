-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_sUp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:46.299252+00:00
-- url     : https://prove2.me/submissions/cfd25c3c-03f3-4a05-9184-432ce3a9c66f

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] {m N : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K) :
    sUp (blkM hN A b a d) = sUp A + lastE b := by
  unfold sUp lastE
  rw [← (eN hN).sum_comp, Fintype.sum_sum_type]
  have hinr : ¬ (((eN hN (Sum.inr ())) : Fin N) : ℕ) + 1 < N := by
    rw [eN_inr]
    omega
  simp only [Fintype.univ_unit, Finset.sum_singleton]
  rw [dif_neg hinr, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hlt : ((eN hN (Sum.inl i) : Fin N) : ℕ) + 1 < N := by
    rw [eN_inl]
    omega
  rw [dif_pos hlt]
  by_cases h : i.val + 1 < m
  · have e : (⟨((eN hN (Sum.inl i) : Fin N) : ℕ) + 1, hlt⟩ : Fin N) = eN hN (Sum.inl ⟨i.val + 1, h⟩) := by
      ext
      simp [eN_inl]
    rw [e, blkM_ll, dif_pos h, if_neg (by omega), add_zero]
  · have e : (⟨((eN hN (Sum.inl i) : Fin N) : ℕ) + 1, hlt⟩ : Fin N) = eN hN (Sum.inr ()) := by
      ext
      simp only [eN_inl, eN_inr]
      omega
    rw [e, blkM_lr, dif_neg h, if_pos (by omega), zero_add]
end Formalism.FourierDecayAlt.P.A5x8
