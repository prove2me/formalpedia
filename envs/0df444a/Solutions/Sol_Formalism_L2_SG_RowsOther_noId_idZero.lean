-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.noId_idZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:27.301867+00:00
-- url     : https://prove2.me/submissions/09a11e81-f182-43c5-b88f-1dee24599374

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
import Theorems.Thm_Formalism_L2_SG_RowsOther_noId_idSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
namespace Formalism.L2.SG.RowsOther
theorem _root_.solution : (noId X).IdZero := by
  unfold PB.Terms.IdZero PB.Terms.part
  rw [noId_idSet]
  simp
end Formalism.L2.SG.RowsOther
