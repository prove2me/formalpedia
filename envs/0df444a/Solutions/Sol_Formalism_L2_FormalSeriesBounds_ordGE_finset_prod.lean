-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ordGE_finset_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:06.83407+00:00
-- url     : https://prove2.me/submissions/13b9a52d-4491-472e-bf0b-60b1d5b18969

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul


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
theorem _root_.solution {ι : Type*} (s : Finset ι) (n : ι → ℕ) (f : ι → MvPowerSeries τ C)
    (h : ∀ i ∈ s, OrdGE (n i) (f i)) : OrdGE (∑ i ∈ s, n i) (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using ordGE_zero (1 : MvPowerSeries τ C)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact Formalism.BaseCaseIdentities.OrdGE.mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Formalism.L2.FormalSeriesBounds
