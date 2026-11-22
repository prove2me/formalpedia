-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:11:25.246323+00:00
-- url     : https://prove2.me/submissions/86a37685-7329-4232-9618-501e28155d51

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (r : ℕ) [Fact r.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})] :
    Nat.card (P.inertia Gal(L/ℚ)) = P.ramificationIdx ℤ := by
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : r.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  rw [card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (span {(r : ℤ)}) P,
    ramificationIdxIn_eq_ramificationIdx (span {(r : ℤ)}) P Gal(L/ℚ)]
end Formalism.TwoAdicCyclotomicDecomposition
