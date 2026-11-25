-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:47.933633+00:00
-- url     : https://prove2.me/submissions/9216a354-ea7a-4c25-b1da-6d7333d0b0e7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_al_zeroM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)
namespace Formalism.L2.FormalSeriesBounds
namespace Sys
theorem _root_.solution : (Matrix.of fun c k : I => S.al c 0 k).det ≠ 0 := by
  intro h
  have h1 := S.unimod
  have h2 : (Matrix.of fun c k : I => S.al c 0 k) = Matrix.of S.tan := by
    ext c k
    exact S.al_zeroM c k
  rw [← h2, h, V.v.map_zero] at h1
  exact WithTop.top_ne_zero h1
end Sys
end Formalism.L2.FormalSeriesBounds
