-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.dVar_subst_linS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:30.85096+00:00
-- url     : https://prove2.me/submissions/75ae6c74-ccca-4633-a5b6-d940c17094e7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_dVar_eq_pderiv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_subst_linS

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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {C : Type} [Field C] {σ τ : Type} [Fintype σ] [Fintype τ] (M : τ → σ → C)
    (b : τ) (H : MvPowerSeries σ C) :
    dVar b (subst (linS M) H) = ∑ w, M b w • subst (linS M) (dVar w H) := by
  rw [dVar_eq_pderiv, pderiv_subst_linS]
  exact Finset.sum_congr rfl fun w _ => by rw [dVar_eq_pderiv]
end Formalism.L2.FormalSeriesBounds
