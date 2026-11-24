-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.nonIdentity_K0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:17.054416+00:00
-- url     : https://prove2.me/submissions/2614e874-7cb3-4466-bd47-eec8f9506f60

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
import Theorems.Thm_Formalism_L2_SG_RowsOther_noId_idZero

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
theorem _root_.solution (one : H) (h : IdOne X one) : (noId X).K0 = X.K0 - one := by
  have h0 : (noId X).part (noId X).idSet = 0 := noId_idZero X
  have hg : (noId X).part (noId X).genSet = X.part X.genSet := rfl
  have hn : (noId X).part (noId X).ngSet = X.part X.ngSet := rfl
  unfold IdOne at h
  simp only [PB.Terms.K0]
  rw [h0, hg, hn, h]
  abel
end Formalism.L2.SG.RowsOther
