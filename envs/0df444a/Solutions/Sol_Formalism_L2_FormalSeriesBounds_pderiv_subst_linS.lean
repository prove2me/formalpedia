-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.pderiv_subst_linS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:23:44.089225+00:00
-- url     : https://prove2.me/submissions/4adb2955-4351-4e5f-8890-bdb32a1ab028

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_linS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_linS

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
theorem _root_.solution [Fintype σ] (M : τ → σ → C) (b : τ) (H : MvPowerSeries σ C) :
    pderiv C b (subst (linS M) H) = ∑ w, M b w • subst (linS M) (pderiv C w H) := by
  rw [pderiv_subst (ordGE_linS M)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [pderiv_linS, smul_eq_C_mul]
end Formalism.L2.FormalSeriesBounds
