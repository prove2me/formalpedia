-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.index_zpowers_five
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:42.639662+00:00
-- url     : https://prove2.me/submissions/43e2098d-a706-4614-9d9e-cca93c7cecb1

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset
namespace Formalism.GaloisIrreducibility
theorem _root_.solution (n : ℕ) (h : Nat.Coprime 5 (2 ^ (n + 2))) :
    (Subgroup.zpowers (ZMod.unitOfCoprime 5 h)).index = 2 := by
  have hc := Subgroup.card_mul_index (Subgroup.zpowers (ZMod.unitOfCoprime 5 h))
  rw [Nat.card_zpowers, ← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat,
    ZMod.orderOf_five, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega)] at hc
  have : 2 ^ (n + 2 - 1) * (2 - 1) = 2 ^ n * 2 := by
    rw [show n + 2 - 1 = n + 1 by omega, pow_succ]; norm_num
  rw [this] at hc
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hc
end Formalism.GaloisIrreducibility
