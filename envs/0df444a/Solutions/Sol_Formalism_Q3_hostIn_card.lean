-- Prove2me | solution 1 for Formalism.Q3.hostIn_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:26.642523+00:00
-- url     : https://prove2.me/submissions/eb351168-0966-4910-8a49-a196e5a0f324

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia

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
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (P.inertia Gal(E/ℚ)) = P.ramificationIdx ℤ := by
  have : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  rw [card_inertia_eq_ramificationIdxIn (G := Gal(E/ℚ)) (span {(p : ℤ)}) P,
    ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(E/ℚ)]
end Formalism.Q3
