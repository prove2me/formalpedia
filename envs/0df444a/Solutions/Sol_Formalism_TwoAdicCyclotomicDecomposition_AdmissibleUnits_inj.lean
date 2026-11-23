-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:01:57.436313+00:00
-- url     : https://prove2.me/submissions/95fcbac9-18d6-4f86-ad4d-1aaeb95d94ac

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_orderOf_five_units_two_pow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_sign_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
namespace Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
theorem _root_.solution (n : ℕ) : Function.Injective (fun p : Bool × Fin (2 ^ (n + 1)) =>
    (if p.1 then -1 else 1) * u5 (n + 3) ^ (p.2 : ℕ)) := by
  rintro ⟨b, k⟩ ⟨b', k'⟩ h
  have h' : (if b then -1 else 1) * u5 (n + 3) ^ (k : ℕ) =
      (if b' then -1 else 1) * u5 (n + 3) ^ (k' : ℕ) := h
  have hb : b = b' := sign_eq n h'
  subst hb
  have h2 : u5 (n + 3) ^ (k : ℕ) = u5 (n + 3) ^ (k' : ℕ) := mul_left_cancel h'
  have ho : orderOf (u5 (n + 3)) = 2 ^ (n + 1) := orderOf_five_units_two_pow (n + 1)
  rw [pow_inj_mod, ho, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at h2
  exact Prod.ext rfl (Fin.ext h2)
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
