-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.shape_of_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:14.813966+00:00
-- url     : https://prove2.me/submissions/28e4a8d2-8f60-426f-9145-309cad84b240

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_blk_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_wMat_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_wMat_mulVec_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.ShapeM := by
  intro m t σ X B ρ hX
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun k => ?_, ?_, ?_⟩
  · obtain ⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc :=
      ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc :=
      ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    have hlt : j' < i'.rev := by
      rw [Fin.lt_def, Fin.val_rev]
      simp only [Fin.val_castSucc] at hij
      omega
    rw [Mcoord, blk_cc, wMat_mul_apply]
    simp [Matrix.one_apply, hlt.ne', hX _ _ hlt.le]
  · obtain ⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc :=
      ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc :=
      ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    have heq : i'.rev = j' := by
      apply Fin.ext
      rw [Fin.val_rev]
      simp only [Fin.val_castSucc] at hij
      omega
    rw [Mcoord, blk_cc, wMat_mul_apply, heq]
    simp [hX _ _ le_rfl]
  · rw [Mcoord, xOf]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, blk_cl, blk_cl, wMat_mulVec_apply, Fin.rev_rev]
    · rw [Fin.succ_castSucc, blk_cc, blk_cc, wMat_mul_apply, Fin.rev_rev]
      have hne : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
      simp [Matrix.one_apply, hne]
  · have h0 : (0 : Fin (m + 1 + 1)) = (0 : Fin (m + 1)).castSucc := rfl
    rw [Mcoord, h0, blk_lc]
  · rw [Mcoord, blk_ll]
end Formalism.FourierDecayAlt.P
