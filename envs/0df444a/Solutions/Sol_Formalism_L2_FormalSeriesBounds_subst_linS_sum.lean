-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_linS_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:01:57.446268+00:00
-- url     : https://prove2.me/submissions/7174b7cf-a4ad-412b-8df2-51bd4bc64902

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
theorem _root_.solution [Finite σ] (M : τ → σ → C) {ι : Type*} (s : Finset ι)
    (F : ι → MvPowerSeries σ C) :
    subst (linS M) (∑ i ∈ s, F i) = ∑ i ∈ s, subst (linS M) (F i) := by
  rw [← substAlgHom_apply (hasSubst_linS M), map_sum]
  simp only [substAlgHom_apply]
end Formalism.L2.FormalSeriesBounds
