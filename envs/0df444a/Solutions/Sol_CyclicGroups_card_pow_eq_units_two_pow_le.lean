-- Prove2me | solution 1 for CyclicGroups.card_pow_eq_units_two_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T16:26:45.600499+00:00
-- url     : https://prove2.me/submissions/1da1fa8a-d83c-46ef-a6e6-c69df8f41737

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Maynard.PpRootTwo =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The `(ZMod (2 ^ e))ˣ` `k`-th-root count (node N-PP-ROOT-TWO)

The GEH door's `PpLevel` 2-corner. For `e ≥ 3`, `(ZMod (2 ^ e))ˣ ≅ C₂ × C_{2^{e-2}}`,
so the number of `k`-th roots of any unit is at most `gcd(k, 2) · gcd(k, 2^{e-2})`.
Specialized to `k = 2` this gives the uniform bound `≤ 4` for every modulus `2 ^ e`,
which is what the CRT fold consumes.

The `C₂` factor is realized as the reduction quotient `ρ : (ZMod (2^e))ˣ →* (ZMod 4)ˣ`
(`ZMod.unitsMap`, surjective), and the `C_{2^{e-2}}` factor as its kernel, which is
cyclic because it contains the unit `5` whose order is `2^{e-2}` (`ZMod.orderOf_five`)
and has the matching cardinality (Lagrange). We never need to name `-1`.

## Main results

* `PpRootTwo.card_pow_eq_le_card_ker` — general: `#{x | x^k = a} ≤ |ker(x ↦ x^k)|`.
* `PpRootTwo.card_ker_le_of_cyclic_ext` — abstract keystone: for a surjection onto a
  cyclic group with cyclic kernel, the `k`-torsion count is submultiplicative.
* `card_pow_eq_units_two_pow_le` — primary: modulus `2^(n+2)`, bound `gcd k 2 · gcd k (2^n)`.
* `card_pow_eq_units_two_pow_le'` — the `e ≥ 3` phrasing with `2^(e-2)`.
* `card_sq_eq_units_two_pow_le_four` — the priority deliverable: `k = 2`, `≤ 4`, all `e`.
-/

open Finset

namespace Salt.Maynard.PpRootTwo

/-- In any finite commutative group, the number of `k`-th roots of `a` is at most the
cardinality of the `k`-th-power kernel: nonempty fibres of `x ↦ x^k` are all equinumerous
with the identity fibre, which is the kernel. -/
theorem card_pow_eq_le_card_ker {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) (a : G) :
    (univ.filter (fun x : G => x ^ k = a)).card
      ≤ Nat.card (powMonoidHom k : G →* G).ker := by
  have hker : (univ.filter (fun x : G => x ^ k = 1)).card
      = Nat.card (powMonoidHom k : G →* G).ker := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply])
  by_cases ha : a ∈ Set.range (powMonoidHom k : G →* G)
  · have h1 : (1 : G) ∈ Set.range (powMonoidHom k : G →* G) := ⟨1, one_pow k⟩
    have hfib := MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom k : G →* G) ha h1
    simp only [powMonoidHom_apply] at hfib
    rw [hfib, hker]
  · have hempty : univ.filter (fun x : G => x ^ k = a) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _ hx
      exact ha ⟨x, by rw [powMonoidHom_apply]; exact hx⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

/-- **Abstract keystone.** Let `ρ : G →* Q` be a homomorphism of finite commutative groups
with `Q` cyclic and `ker ρ` cyclic. Then the `k`-torsion count of `G` is submultiplicative
across the extension `1 → ker ρ → G → im ρ → 1`:
`|ker(x ↦ x^k)| ≤ gcd(|ker ρ|, k) · gcd(|Q|, k)`.

Proof: restrict `ρ` to the torsion subgroup `T = ker(x ↦ x^k)`. By Lagrange
`|T| = |ker(ρ|_T)| · |im(ρ|_T)|`. The image lands in the `k`-torsion of the cyclic `Q`
(count `gcd(|Q|,k)`); the kernel is `T ⊓ ker ρ`, the `k`-torsion of the cyclic `ker ρ`
(count `gcd(|ker ρ|,k)`). -/
theorem card_ker_le_of_cyclic_ext {G Q : Type*}
    [CommGroup G] [Finite G] [CommGroup Q] [Finite Q]
    (ρ : G →* Q) [IsCyclic Q] [IsCyclic ρ.ker] (k : ℕ) :
    Nat.card (powMonoidHom k : G →* G).ker
      ≤ Nat.gcd (Nat.card ρ.ker) k * Nat.gcd (Nat.card Q) k := by
  set T := (powMonoidHom k : G →* G).ker with hT
  set f : T →* Q := ρ.comp T.subtype with hf
  -- Lagrange for the restricted map `f = ρ|_T`.
  have hlag : Nat.card ↥f.ker * Nat.card ↥f.range = Nat.card ↥T := by
    have h := f.ker.card_mul_index
    rwa [Subgroup.index_ker f] at h
  -- The image of the torsion is contained in the torsion of `Q`.
  have hrange_le : f.range ≤ (powMonoidHom k : Q →* Q).ker := by
    intro y hy
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have ht : (t : G) ^ k = 1 := by
      have h2 := MonoidHom.mem_ker.mp t.2
      rwa [powMonoidHom_apply] at h2
    have hft : f t = ρ (t : G) := rfl
    rw [hft, ← map_pow, ht, map_one]
  have hrange_card : Nat.card ↥f.range ≤ Nat.gcd (Nat.card Q) k := by
    have hle : Nat.card ↥f.range ≤ Nat.card ↥(powMonoidHom k : Q →* Q).ker :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hrange_le)
        (Subgroup.inclusion_injective hrange_le)
    rwa [IsCyclic.card_powMonoidHom_ker] at hle
  -- The kernel of `f` is the `k`-torsion of the cyclic group `ker ρ`.
  have hker_card : Nat.card ↥f.ker = Nat.gcd (Nat.card ρ.ker) k := by
    have hfker : f.ker = ρ.ker.subgroupOf T := by
      rw [hf, ← MonoidHom.comap_ker ρ T.subtype, Subgroup.comap_subtype]
    have ea : Nat.card ↥(ρ.ker.subgroupOf T) = Nat.card ↥(T ⊓ ρ.ker) := by
      rw [← Subgroup.inf_subgroupOf_left ρ.ker T]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have eb : Nat.card ↥(T ⊓ ρ.ker) = Nat.card ↥(T.subgroupOf ρ.ker) := by
      rw [← Subgroup.inf_subgroupOf_right T ρ.ker]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
    have ec : T.subgroupOf ρ.ker = (powMonoidHom k : ρ.ker →* ρ.ker).ker := by
      ext y
      simp only [Subgroup.mem_subgroupOf, hT, MonoidHom.mem_ker, powMonoidHom_apply,
        ← Subgroup.coe_pow, OneMemClass.coe_eq_one]
    rw [hfker, ea, eb, ec, IsCyclic.card_powMonoidHom_ker]
  calc Nat.card ↥T = Nat.card ↥f.ker * Nat.card ↥f.range := hlag.symm
    _ = Nat.gcd (Nat.card ρ.ker) k * Nat.card ↥f.range := by rw [hker_card]
    _ ≤ Nat.gcd (Nat.card ρ.ker) k * Nat.gcd (Nat.card Q) k := Nat.mul_le_mul le_rfl hrange_card

/-- **Primary bound** (modulus `2 ^ (n + 2)`, i.e. `e = n + 2 ≥ 2`). The number of `k`-th
roots of any unit `a ∈ (ZMod (2^(n+2)))ˣ` is at most `gcd(k, 2) · gcd(k, 2^n)`.

The `C₂` factor is the reduction `ρ = ZMod.unitsMap : (ZMod (2^(n+2)))ˣ →* (ZMod 4)ˣ`
(surjective); the `C_{2^n}` factor is `ker ρ`, cyclic because it contains the unit `5`,
whose order is `2^n` (`ZMod.orderOf_five`) and which equals `|ker ρ| = 2^n` (Lagrange). -/
theorem card_pow_eq_units_two_pow_le {n : ℕ} (k : ℕ) (a : (ZMod (2 ^ (n + 2)))ˣ) :
    (univ.filter (fun x : (ZMod (2 ^ (n + 2)))ˣ => x ^ k = a)).card
      ≤ Nat.gcd k 2 * Nat.gcd k (2 ^ n) := by
  classical
  haveI hnz : NeZero (2 ^ (n + 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  haveI : IsCyclic (ZMod 4)ˣ := ZMod.isCyclic_units_four
  have hdvd : (4 : ℕ) ∣ 2 ^ (n + 2) := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4]; exact pow_dvd_pow 2 (by omega)
  set ρ : (ZMod (2 ^ (n + 2)))ˣ →* (ZMod 4)ˣ := ZMod.unitsMap hdvd with hρ
  have hsurj : Function.Surjective ρ := ZMod.unitsMap_surjective hdvd
  have hcardQ : Nat.card (ZMod 4)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; decide
  have hcardG : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ (n + 1) := by
    have htot : Nat.totient (2 ^ (n + 2)) = 2 ^ (n + 1) := by
      rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < n + 2)]
      rw [show n + 2 - 1 = n + 1 by omega]; norm_num
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, htot]
  -- The unit `5`, its order, and its membership in `ker ρ`.
  have hcop : Nat.Coprime 5 (2 ^ (n + 2)) := Nat.Coprime.pow_right _ (by decide)
  set u5 : (ZMod (2 ^ (n + 2)))ˣ := ZMod.unitOfCoprime 5 hcop with hu5
  have hu5nat : (↑u5 : ZMod (2 ^ (n + 2))) = ((5 : ℕ) : ZMod (2 ^ (n + 2))) :=
    ZMod.coe_unitOfCoprime 5 hcop
  have hu5order : orderOf u5 = 2 ^ n := by
    rw [← orderOf_units, hu5nat, Nat.cast_ofNat, ZMod.orderOf_five]
  have hρu5 : ρ u5 = 1 := by
    apply Units.ext
    have hval : (↑(ρ u5) : ZMod 4)
        = ZMod.castHom hdvd (ZMod 4) (↑u5 : ZMod (2 ^ (n + 2))) := by
      rw [hρ, ZMod.unitsMap_val, ZMod.castHom_apply]
    rw [hval, hu5nat, map_natCast, Units.val_one]; decide
  have hu5mem : u5 ∈ ρ.ker := MonoidHom.mem_ker.mpr hρu5
  -- `|ker ρ| = 2^n` by Lagrange (`ρ` surjective onto the order-`2` group `(ZMod 4)ˣ`).
  have hcardker : Nat.card ↥ρ.ker = 2 ^ n := by
    have hidx : ρ.ker.index = 2 := by
      rw [Subgroup.index_ker ρ,
        show ρ.range = ⊤ from MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcardQ]
    have hmul := ρ.ker.card_mul_index
    rw [hidx, hcardG, show (2 : ℕ) ^ (n + 1) = 2 ^ n * 2 from by rw [pow_succ]] at hmul
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hmul
  -- `ker ρ` is cyclic: it contains `5`, whose order equals its cardinality.
  haveI hcyc : IsCyclic ↥ρ.ker :=
    isCyclic_of_orderOf_eq_card ⟨u5, hu5mem⟩ (by rw [Subgroup.orderOf_mk, hu5order, hcardker])
  calc (univ.filter (fun x : (ZMod (2 ^ (n + 2)))ˣ => x ^ k = a)).card
      ≤ Nat.card (powMonoidHom k :
          (ZMod (2 ^ (n + 2)))ˣ →* (ZMod (2 ^ (n + 2)))ˣ).ker := card_pow_eq_le_card_ker k a
    _ ≤ Nat.gcd (Nat.card ρ.ker) k * Nat.gcd (Nat.card (ZMod 4)ˣ) k :=
        card_ker_le_of_cyclic_ext ρ k
    _ = Nat.gcd (2 ^ n) k * Nat.gcd 2 k := by rw [hcardker, hcardQ]
    _ = Nat.gcd k 2 * Nat.gcd k (2 ^ n) := by
        rw [Nat.gcd_comm (2 ^ n) k, Nat.gcd_comm 2 k, Nat.mul_comm]

/-- The `e ≥ 3` phrasing of the primary bound, with the exponent `2 ^ (e - 2)`. -/
theorem card_pow_eq_units_two_pow_le' {e : ℕ} (he : 3 ≤ e) (k : ℕ)
    (a : (ZMod (2 ^ e))ˣ) :
    (univ.filter (fun x : (ZMod (2 ^ e))ˣ => x ^ k = a)).card
      ≤ Nat.gcd k 2 * Nat.gcd k (2 ^ (e - 2)) := by
  obtain ⟨n, rfl⟩ := le_iff_exists_add'.mp (show 2 ≤ e by omega)
  rw [show n + 2 - 2 = n by omega]
  exact card_pow_eq_units_two_pow_le k a

/-- **Priority deliverable.** At `k = 2` the root count is `≤ 4` for every modulus `2 ^ e`
(all `e`); this uniform bound is what the CRT fold consumes. -/
theorem card_sq_eq_units_two_pow_le_four (e : ℕ) (a : (ZMod (2 ^ e))ˣ) :
    (univ.filter (fun x : (ZMod (2 ^ e))ˣ => x ^ 2 = a)).card ≤ 4 := by
  classical
  rcases lt_or_ge e 2 with he | he
  · -- `e ∈ {0, 1}`: at most `Fintype.card ≤ 2 ≤ 4` units.
    have hsub : (univ.filter (fun x : (ZMod (2 ^ e))ˣ => x ^ 2 = a)).card
        ≤ Fintype.card (ZMod (2 ^ e))ˣ := by
      rw [← Finset.card_univ]; exact Finset.card_filter_le _ _
    have hcard : Fintype.card (ZMod (2 ^ e))ˣ ≤ 4 := by interval_cases e <;> decide
    exact hsub.trans hcard
  · obtain ⟨n, rfl⟩ := le_iff_exists_add'.mp he
    have h := card_pow_eq_units_two_pow_le (n := n) 2 a
    have hg2 : Nat.gcd 2 (2 ^ n) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 2 (2 ^ n))
    calc (univ.filter (fun x : (ZMod (2 ^ (n + 2)))ˣ => x ^ 2 = a)).card
        ≤ Nat.gcd 2 2 * Nat.gcd 2 (2 ^ n) := h
      _ ≤ 2 * 2 := by
          rw [show Nat.gcd 2 2 = 2 from by decide]; exact Nat.mul_le_mul le_rfl hg2
      _ = 4 := by norm_num

end Salt.Maynard.PpRootTwo

end




theorem solution {n : ℕ} (k : ℕ) (a : (ZMod (2 ^ (n + 2)))ˣ) :
    (Finset.univ.filter (fun x : (ZMod (2 ^ (n + 2)))ˣ => x ^ k = a)).card
      ≤ Nat.gcd k 2 * Nat.gcd k (2 ^ n) :=
  Salt.Maynard.PpRootTwo.card_pow_eq_units_two_pow_le k a

