-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.block_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:38:34.611092+00:00
-- url     : https://prove2.me/submissions/7497ec82-66ef-4de2-b9c6-d2fe8a3f96eb

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_qf_block
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
variable {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β)
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {a : α → α → ℂ} {w : α → β → ℂ} {b : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b)
    (c : α → ℂ) (d : β → ℂ) :
    0 ≤ (qf Y₁ a c).re + (qf Y₂ b d).re + 2 * (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c p) * w p q * d q).re := by
  have h1 := ((psd_iff_qf _ _).1 ((blockPSD_iff Y₁ Y₂ a w b).1 h)).2 (Sum.elim c d)
  rw [qf_block] at h1
  simpa using h1
end Formalism.FourierDecayAlt.P.PBA
