-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.coeff_subst_ze
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:45.846022+00:00
-- url     : https://prove2.me/submissions/85f46a1b-9c24-4297-92ad-e5da43668977

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_smul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_linS_congr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_ze_partial

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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)
variable {τ : Type} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds
namespace Sys
theorem _root_.solution (W : τ → I → C) {t : I → MvPowerSeries I C} (ht : S.IsT t) (κ : J)
    (A : τ →₀ ℕ) :
    coeff A (subst (linS W) (S.ze t κ)) =
      -∑ c, ∑ j ∈ Finset.Icc 1 A.degree,
        S.be c j κ * coeff A (subst (linS W) (t c) ^ (V.l ^ j)) := by
  rw [coeff_subst_linS_congr W (fun μ hμ => S.ze_partial ht κ A.degree μ hμ) A le_rfl,
    subst_linS_neg, subst_linS_sum, map_neg, map_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [subst_linS_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [subst_linS_smul, subst_linS_pow, map_smul, smul_eq_mul]
end Sys
end Formalism.L2.FormalSeriesBounds
