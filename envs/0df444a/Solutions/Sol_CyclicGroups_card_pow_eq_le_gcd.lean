-- Prove2me | solution 1 for CyclicGroups.card_pow_eq_le_gcd
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T12:54:06.259498+00:00
-- url     : https://prove2.me/submissions/ce6dbc57-e049-4621-83a3-169856188d8e

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Maynard.PpRootCyc =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The abstract cyclic-group `k`-th-root count (node N-PP-ROOT-CYC)

Root of the GEH door's `PpLevel` chain. In a finite cyclic commutative group the
number of `k`-th roots of any element is at most `gcd(k, |G|)`. Specialized to
`(ZMod (p ^ e))ˣ` for an odd prime `p` this counts square roots (`k = 2`) by at
most `2`.

## Main results

* `card_pow_eq_le_gcd` — abstract cyclic keystone: `#{x | x^k = a} ≤ gcd(k, |G|)`.
* `card_pow_eq_le_gcd_units_prime_pow` — the `(ZMod (p ^ e))ˣ` wrapper, bound
  `gcd(k, φ(p^e))`.
* `card_sq_eq_le_two_units_prime_pow` — the `k = 2` corollary: at most `2` square
  roots in `(ZMod (p ^ e))ˣ` for odd `p`, `e ≥ 1`.

The proof route: fibers of `powMonoidHom k : G →* G` in a finite group are all
equicardinal (`MonoidHom.card_fiber_eq_of_mem_range`); the identity fiber is the
kernel, of size `gcd(|G|, k)` in the cyclic case
(`IsCyclic.card_powMonoidHom_ker`).
-/

namespace Salt.Maynard

open Finset

/-- In a finite cyclic commutative group, the number of `k`-th roots of any
element is at most `gcd(k, |G|)`. -/
theorem card_pow_eq_le_gcd {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    [IsCyclic G] (k : ℕ) (a : G) :
    (Finset.univ.filter (fun x : G => x ^ k = a)).card ≤ Nat.gcd k (Fintype.card G) := by
  -- Bridge the `1`-fiber (as a filter) to the kernel of `powMonoidHom k`.
  have hker : (Finset.univ.filter (fun x : G => x ^ k = 1)).card
      = Nat.card (powMonoidHom k : G →* G).ker := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply])
  by_cases ha : a ∈ Set.range (powMonoidHom k : G →* G)
  · -- `a` is a `k`-th power: all nonempty fibers are equicardinal, and the
    -- identity fiber is the kernel, of cardinality `gcd(|G|, k)`.
    have h1 : (1 : G) ∈ Set.range (powMonoidHom k : G →* G) := ⟨1, one_pow k⟩
    have hfib := MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom k : G →* G) ha h1
    simp only [powMonoidHom_apply] at hfib
    rw [hfib, hker, IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card]
    exact le_of_eq (Nat.gcd_comm _ _)
  · -- `a` is not a `k`-th power: the fiber is empty.
    have hempty : Finset.univ.filter (fun x : G => x ^ k = a) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hx
      exact ha ⟨x, by rw [powMonoidHom_apply]; exact hx⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

/-- The `(ZMod (p ^ e))ˣ` specialization for an odd prime power: the number of
`k`-th roots of any unit is at most `gcd(k, φ(p^e))`.

The `letI` provides `NeZero (p ^ e)` (from `hp.ne_zero`) so that `Fintype (ZMod
(p^e))ˣ` — needed to form `Finset.univ` — elaborates in the statement. It adds no
mathematical hypothesis: `NeZero (p ^ e)` is a consequence of `hp`. -/
theorem card_pow_eq_le_gcd_units_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ℕ) (_he : 1 ≤ e) (k : ℕ) (a : (ZMod (p ^ e))ˣ) :
    letI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
    (Finset.univ.filter (fun x : (ZMod (p ^ e))ˣ => x ^ k = a)).card
      ≤ Nat.gcd k (Nat.totient (p ^ e)) := by
  haveI hne : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  haveI hcyc : IsCyclic (ZMod (p ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have h := card_pow_eq_le_gcd (G := (ZMod (p ^ e))ˣ) k a
  rwa [ZMod.card_units_eq_totient] at h

/-- For an odd prime power `p^e` (`p ≠ 2`, `e ≥ 1`), `φ(p^e)` is even, so
`gcd(2, φ(p^e)) = 2`. -/
theorem gcd_two_totient_eq_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ)
    (he : 1 ≤ e) : Nat.gcd 2 (Nat.totient (p ^ e)) = 2 := by
  have hp2' : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hlt : 2 < p ^ e :=
    lt_of_lt_of_le hp2' (le_self_pow (le_of_lt (lt_trans one_lt_two hp2'))
      (Nat.one_le_iff_ne_zero.mp he))
  exact Nat.gcd_eq_left (Even.two_dvd (Nat.totient_even hlt))

/-- The `k = 2` corollary: in `(ZMod (p ^ e))ˣ` for an odd prime power there are at
most `2` square roots of any unit. (`letI` as in the wrapper above.) -/
theorem card_sq_eq_le_two_units_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ℕ) (he : 1 ≤ e) (a : (ZMod (p ^ e))ˣ) :
    letI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
    (Finset.univ.filter (fun x : (ZMod (p ^ e))ˣ => x ^ 2 = a)).card ≤ 2 := by
  haveI hne : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have h := card_pow_eq_le_gcd_units_prime_pow hp hp2 e he 2 a
  rwa [gcd_two_totient_eq_two hp hp2 e he] at h

end Salt.Maynard

end




theorem solution {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (k : ℕ) (a : G) :
    (Finset.univ.filter (fun x : G => x ^ k = a)).card ≤ Nat.gcd k (Fintype.card G) :=
  Salt.Maynard.card_pow_eq_le_gcd k a

