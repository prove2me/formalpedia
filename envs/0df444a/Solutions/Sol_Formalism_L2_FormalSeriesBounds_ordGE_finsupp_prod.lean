-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ordGE_finsupp_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:26:46.955126+00:00
-- url     : https://prove2.me/submissions/79f3869e-264f-4e48-8d06-bee676c5267c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_finset_prod
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow


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
theorem _root_.solution (a : σ → MvPowerSeries τ C) (ha : ∀ s, OrdGE 1 (a s)) (d : σ →₀ ℕ) :
    OrdGE d.degree (d.prod fun s n => a s ^ n) := by
  have h := ordGE_finset_prod d.support (fun s => d s) (fun s => a s ^ d s)
    (fun s _ => Formalism.BaseCaseIdentities.OrdGE.pow (ha s) (d s))
  exact h
end Formalism.L2.FormalSeriesBounds
