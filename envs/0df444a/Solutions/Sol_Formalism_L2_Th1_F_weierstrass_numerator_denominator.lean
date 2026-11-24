-- Prove2me | solution 1 for Formalism.L2.Th1.F.weierstrass_numerator_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:35:14.035315+00:00
-- url     : https://prove2.me/submissions/599f7a4b-8545-4fe5-9113-1d50500fe3aa

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Theorems.Thm_Formalism_L2_Th1_F_POf_coeff_pOf

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
open Formalism.L2.Th1.CM (cW wpNum wpDen)
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open POf
namespace Formalism.L2.Th1.F
theorem _root_.solution : WpNumDen := by
  intro K _ _ g2 g3
  constructor
  · ext n
    rw [map_add, coeff_X_pow_mul', coeff_one]
    rcases n with _ | _ | n
    · simp [wpNum]
    · simp [wpNum]
    · rw [if_neg (by omega), if_pos (by omega), zero_add, show n + 1 + 1 - 2 = n from rfl]
      simp [pOf]
  · ext n
    rw [map_sub, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one]
    rcases n with _ | _ | _ | n
    · simp [wpDen]
    · simp [wpDen]
    · simp [wpDen]
    · rw [if_neg (by omega), if_pos (by omega), show n + 1 + 1 + 1 - 3 = n from rfl, coeff_derivative, coeff_pOf]
      unfold wpDen
      rw [coeff_mk, if_neg (by omega)]
      have e1 : Even (n + 1 + 1 + 1) ↔ Even (n + 1) := by simp [Nat.even_add]
      simp only [e1]
      by_cases he : Even (n + 1)
      · rw [if_pos he, if_pos he]
        obtain ⟨a, ha⟩ := he
        have e2 : (n + 1 + 1 + 1) / 2 = a + 1 := by omega
        have e3 : (n + 1) / 2 + 1 = a + 1 := by omega
        have e4 : (n : K) + 1 = 2 * a := by
          have : ((n + 1 : ℕ) : K) = ((a + a : ℕ) : K) := by rw [ha]
          push_cast at this; linear_combination this
        rw [e2, e3, e4]
        push_cast
        ring
      · rw [if_neg he, if_neg he]; simp
end Formalism.L2.Th1.F
