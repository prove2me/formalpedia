-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FrobP.valuation_coeff_pow_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:12.721163+00:00
-- url     : https://prove2.me/submissions/e0dafd5b-a80b-4607-b5ce-563cce2bf58f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_valuation_coeff_mul_nonneg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open Formalism.L2.FormalSeriesBounds.FrobP
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.FrobP
theorem _root_.solution {f : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f)) (k : ℕ) :
    ∀ n, V.Ge 0 (PowerSeries.coeff n (f ^ k)) := by
  induction k with
  | zero =>
    intro n
    unfold VF.Ge
    rw [pow_zero, PowerSeries.coeff_one, WithTop.coe_zero]
    split_ifs
    · rw [AddValuation.map_one]
    · rw [AddValuation.map_zero]
      exact le_top
  | succ k ih =>
    rw [pow_succ]
    exact valuation_coeff_mul_nonneg ih hf
end Formalism.L2.FormalSeriesBounds.FrobP
