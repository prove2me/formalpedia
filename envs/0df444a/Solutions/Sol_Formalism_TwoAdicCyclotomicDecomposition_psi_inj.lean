-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.psi_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:22:37.859857+00:00
-- url     : https://prove2.me/submissions/eb9704ec-5f19-461a-b66f-793c734f1874

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_iota_neg
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_iota_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_mod_four_generator_eq_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_psi_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {s m : ℕ} (h : s ≤ m) : Function.Injective (psi h) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨e, k⟩ hk
  rw [psi_apply] at hk
  have h1 : iota (m + 2) e * wgen s m ^ (Multiplicative.toAdd k).val = 1 := congrArg Prod.fst hk
  have he : e = 1 := by
    rcases Int.units_eq_one_or e with rfl | rfl
    · rfl
    · exfalso
      have h2 := congrArg (r4 m) h1
      rw [map_mul, map_pow, mod_four_generator_eq_one, one_pow, mul_one, iota_neg, mod_four_reduction_neg_one, map_one] at h2
      exact neg_one_ne_one_units_zmod_four h2
  subst he
  rw [iota_one, one_mul, ← orderOf_dvd_iff_pow_eq_one, ord_w h] at h1
  have hlt := ZMod.val_lt (Multiplicative.toAdd k)
  have h0 : (Multiplicative.toAdd k).val = 0 := Nat.eq_zero_of_dvd_of_lt h1 hlt
  rw [ZMod.val_eq_zero] at h0
  refine Prod.ext rfl ?_
  show k = 1
  rw [← ofAdd_toAdd k, h0, ofAdd_zero]
end Formalism.TwoAdicCyclotomicDecomposition
