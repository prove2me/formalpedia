-- Prove2me | solution 1 for Formalism.L2.G.RelativeIndexFlags.Core.rowAct_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:36:56.080803+00:00
-- url     : https://prove2.me/submissions/0de37c09-0e08-4341-a248-92b142ddd743

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_IntegralWeylLatticeSpan_WeylEqSpanInt
import Theorems.Thm_Formalism_L2_G_RelativeIndexFlags_Core_rowAct_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowActMul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Matrix Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core
namespace Formalism.L2.G.RelativeIndexFlags.Core
theorem _root_.solution {R : Type} [CommRing R] {r n : ℕ} (g gi : Matrix (Fin r) (Fin r) R) (h : gi * g = 1)
    (F : MvPolynomial (Fin r × Fin n) R) : rowAct R g (rowAct R gi F) = F := by
  have h1 := rowActMul R r n g gi
  rw [h] at h1
  have h2 := congrArg (fun f => f F) h1
  simp only [AlgHom.comp_apply] at h2
  rw [h2, rowAct_one]
end Formalism.L2.G.RelativeIndexFlags.Core
