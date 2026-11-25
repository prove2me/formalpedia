-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ordGE_linS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:55:26.607798+00:00
-- url     : https://prove2.me/submissions/9fa3d685-2f1d-4753-8a01-d9400d300620

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (M : τ → σ → C) (w : σ) : OrdGE 1 (linS M w) := by
  unfold linS
  refine Formalism.BaseCaseIdentities.OrdGE.sum _ fun c _ => ?_
  rw [smul_eq_C_mul]
  exact Formalism.BaseCaseIdentities.OrdGE.C_mul _ (Formalism.BaseCaseIdentities.OrdGE.X c)
end Formalism.L2.FormalSeriesBounds
