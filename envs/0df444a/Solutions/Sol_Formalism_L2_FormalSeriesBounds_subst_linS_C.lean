-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_linS_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:03.364437+00:00
-- url     : https://prove2.me/submissions/13bb662c-f324-4b99-8e13-a7390f67671e

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
theorem _root_.solution [Finite σ] (M : τ → σ → C) (r : C) :
    subst (linS M) (MvPowerSeries.C r : MvPowerSeries σ C) = MvPowerSeries.C r := by
  rw [← substAlgHom_apply (hasSubst_linS M)]
  exact (substAlgHom (hasSubst_linS M)).commutes r
end Formalism.L2.FormalSeriesBounds
