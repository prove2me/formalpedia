-- Prove2me | solution 1 for Formalism.BehrendSets.Ord.card_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:50.206141+00:00
-- url     : https://prove2.me/submissions/6e9faa55-156e-42cf-a5e2-63798a3513e2

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoPowDvdPowTwoPowSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Ord
namespace Formalism.BehrendSets.Ord
theorem _root_.solution (s : ℕ) : Nat.card (ZMod (2 ^ (s + 2)))ˣ = 2 ^ (s + 1) := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega)]
  simp
end Formalism.BehrendSets.Ord
