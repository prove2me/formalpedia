-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:00:59.692586+00:00
-- url     : https://prove2.me/submissions/7457355a-b581-48aa-ab47-6666f7334d07

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_of_ordGE
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_killV

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
theorem _root_.solution [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) (P : σ → Prop)
    (hP : ∀ w, ¬ P w → a w = 0) (F : MvPowerSeries σ C) :
    subst a (killV P F) = subst a F := by
  ext e
  rw [coeff_subst (hasSubst_of_ordGE ha), coeff_subst (hasSubst_of_ordGE ha)]
  refine finsum_congr fun d => ?_
  by_cases hd : ∀ w ∈ d.support, P w
  · rw [coeff_killV, if_pos hd]
  · simp only [not_forall] at hd
    obtain ⟨w, hw, hPw⟩ := hd
    have h0 : (d.prod fun s n => a s ^ n) = 0 := by
      refine Finset.prod_eq_zero hw ?_
      show a w ^ d w = 0
      rw [hP w hPw, zero_pow (Finsupp.mem_support_iff.1 hw)]
    rw [h0, map_zero, smul_zero, smul_zero]
end Formalism.L2.FormalSeriesBounds
