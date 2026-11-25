-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rename_subst_linS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:57:30.666042+00:00
-- url     : https://prove2.me/submissions/85bff92f-ddd8-4c50-b521-517fe6c65cf9

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
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ τ τ' : Type} [Fintype σ] [Fintype τ] (f : τ ↪ τ') (M : τ → σ → C)
    (F : MvPowerSeries σ C) :
    rename f (subst (linS M) F) = subst (fun x => rename f (linS M x)) F := by
  rw [rename_eq_subst, subst_comp_subst_apply (hasSubst_linS M) (HasSubst.X_comp _)]
  congr 1
  funext x
  rw [rename_eq_subst]
end Formalism.L2.FormalSeriesBounds
