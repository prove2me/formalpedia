-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_linS_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:58:03.202565+00:00
-- url     : https://prove2.me/submissions/371d57ac-a2ea-43be-92cc-48e450459989

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_linS

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
theorem _root_.solution [Finite σ] {ρ : Type*} [Finite ρ] (M : τ → σ → C)
    {a : ρ → MvPowerSeries σ C} (ha : ∀ s, constantCoeff (a s) = 0) (γ : MvPowerSeries ρ C) :
    subst (linS M) (subst a γ) = subst (fun s => subst (linS M) (a s)) γ :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (hasSubst_linS M) γ
end Formalism.L2.FormalSeriesBounds
