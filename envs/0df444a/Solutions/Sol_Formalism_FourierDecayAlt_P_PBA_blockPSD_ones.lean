-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.blockPSD_ones
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:38:33.83746+00:00
-- url     : https://prove2.me/submissions/b002f1ac-ae4b-4542-b94f-67a37b6b4e49

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_psd_iff_qf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β) :
    KB.BlockPSD Y₁ Y₂ (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) := by
  rw [blockPSD_iff, psd_iff_qf]
  refine ⟨fun x _ y _ => ?_, fun c => ?_⟩
  · cases x <;> cases y <;> simp [blockK]
  · have hq : qf (Y₁.disjSum Y₂) (blockK (fun _ _ => (1 : ℂ)) (fun _ _ => 1) (fun _ _ => 1)) c =
        conj (∑ x ∈ Y₁.disjSum Y₂, c x) * ∑ x ∈ Y₁.disjSum Y₂, c x := by
      unfold qf
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      cases x <;> cases y <;> simp [blockK]
    rw [hq, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_nonneg]
end Formalism.FourierDecayAlt.P.PBA
