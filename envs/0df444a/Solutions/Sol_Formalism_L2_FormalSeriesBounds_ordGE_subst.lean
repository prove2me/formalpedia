-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ordGE_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:49.220933+00:00
-- url     : https://prove2.me/submissions/db674c7e-1cff-4888-9d86-202b59ce617a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_finsupp_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_of_ordGE

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
variable {C : Type*} [Field C] {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {F : MvPowerSeries σ C} {n : ℕ} (hF : OrdGE n F) : OrdGE n (subst a F) := by
  intro e he
  rw [coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : d.degree < n
  · rw [hF d hd, zero_smul]
  · rw [ordGE_finsupp_prod a ha d e (by omega), smul_zero]
end Formalism.L2.FormalSeriesBounds
