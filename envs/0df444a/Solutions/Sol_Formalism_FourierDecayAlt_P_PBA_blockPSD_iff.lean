-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.blockPSD_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:20:34.187242+00:00
-- url     : https://prove2.me/submissions/811bf6ec-b257-4333-a025-1bd5ad5eb835

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz

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
theorem _root_.solution (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) :
    KB.BlockPSD Y₁ Y₂ a w b ↔ TB.PSDOn (Y₁.disjSum Y₂) (blockK a w b) := by
  unfold KB.BlockPSD blockK
  exact Iff.rfl
end Formalism.FourierDecayAlt.P.PBA
