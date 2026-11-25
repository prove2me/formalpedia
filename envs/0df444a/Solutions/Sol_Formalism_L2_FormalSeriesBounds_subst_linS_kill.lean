-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_linS_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:13:09.825824+00:00
-- url     : https://prove2.me/submissions/eb3cc864-cea9-4d72-8fbc-999d5f306811

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_kill
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_linS

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
theorem _root_.solution [Finite σ] (M : τ → σ → C) (P : σ → Prop) (hP : ∀ w, ¬ P w → ∀ c, M c w = 0)
    (F : MvPowerSeries σ C) : subst (linS M) (killV P F) = subst (linS M) F := by
  refine subst_kill (ordGE_linS M) P (fun w hw => ?_) F
  unfold linS
  exact Finset.sum_eq_zero fun c _ => by rw [hP w hw c, zero_smul]
end Formalism.L2.FormalSeriesBounds
