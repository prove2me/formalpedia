-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.comp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:13.42183+00:00
-- url     : https://prove2.me/submissions/20c3d6c0-c4de-4f76-83c7-295447a9fc3e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution (lam : K →ₗ[ℚ] ℚ) : comp lam (0 : MvPolynomial σ K) = 0 := by
  simp [comp]
end Formalism.L2.FormalSeriesBounds.HaP
