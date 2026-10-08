-- Prove2me | solution 1 for FiniteMagmaE677.exists_e677_not_right_cancellable_496
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T01:22:33.667984+00:00
-- url     : https://prove2.me/submissions/35d8de1f-7c60-425f-bed6-594b8eea28f5

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Definitions.Def_FiniteMagmaE677
import Definitions.Def_FiniteMagmaE677_magma496
import Theorems.Thm_FiniteMagmaE677_magma496_generic

/-!
# A finite E677 magma with 496 elements that is not right-cancellative

Instantiating the generic 496-element construction at `M = GF(2,4)`. The
multiplicative group of `GF(2,4)` is cyclic of order 15; a generator `g`
yields `ζ = g³` (order five) and `ω = g⁵` (order three), whose cyclotomic
relations follow by factoring `X⁵ − 1` and `X³ − 1`. The characteristic is
two, so the generic theorem applies and equips `ZMod 31 × GF(2,4)` (of
cardinality `31 · 16 = 496`) with an E677 magma which is not
right-cancellative — the first explicit finite non-right-cancellative model
of equation 677 on the platform, matching the blueprint's Chapter 13.
-/

universe u

theorem FiniteMagmaE677.exists_e677_not_right_cancellable_496 :
    ∃ (α : Type) (_ : Fintype α) (op : α → α → α),
      Nat.card α = 496 ∧ FiniteMagmaE677.E677 op ∧
      ¬(∀ a b c : α, op a c = op b c → a = b) := by
  haveI hF : Fintype (GaloisField 2 4) := Fintype.ofFinite (GaloisField 2 4)
  have hcardK : Fintype.card (GaloisField 2 4) = 16 := by
    have h := GaloisField.card 2 4 (by norm_num)
    rw [Nat.card_eq_fintype_card] at h
    simpa using h
  haveI : DecidableEq (GaloisField 2 4) := Classical.decEq _
  have hcardU : Fintype.card (GaloisField 2 4)ˣ = 15 := by
    rw [Fintype.card_units, hcardK]
    try norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField 2 4)ˣ)
  have hord : orderOf g = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcardU]
  have hgp15 : (g : GaloisField 2 4) ^ 15 = 1 := by
    have h1 : g ^ orderOf g = 1 := pow_orderOf_eq_one g
    rw [hord] at h1
    rw [← Units.val_pow_eq_pow_val, h1]
    exact Units.val_one
  have hζ5 : ((g : GaloisField 2 4) ^ 3) ^ 5 = 1 := by
    rw [← pow_mul, show 3 * 5 = 15 by norm_num]
    exact hgp15
  have hζne : ¬((g : GaloisField 2 4) ^ 3 = 1) := by
    intro h
    have h' : g ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)
    have hdvd : 15 ∣ 3 := by
      have h2 := (orderOf_dvd_iff_pow_eq_one).symm.mp h'
      rw [hord] at h2
      exact h2
    omega
  have hζ : ((g : GaloisField 2 4) ^ 3) ^ 4 + ((g : GaloisField 2 4) ^ 3) ^ 3
      + ((g : GaloisField 2 4) ^ 3) ^ 2 + (g : GaloisField 2 4) ^ 3 + 1 = 0 := by
    have hexpand : ∀ x : GaloisField 2 4,
        (x - 1) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = x ^ 5 - 1 := by intro x; ring
    have hfac : ((g : GaloisField 2 4) ^ 3 - 1) *
        (((g : GaloisField 2 4) ^ 3) ^ 4 + ((g : GaloisField 2 4) ^ 3) ^ 3
          + ((g : GaloisField 2 4) ^ 3) ^ 2 + (g : GaloisField 2 4) ^ 3 + 1) = 0 := by
      rw [hexpand, hζ5]
      ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h (sub_ne_zero.mpr hζne)
    · exact h
  have hω3 : ((g : GaloisField 2 4) ^ 5) ^ 3 = 1 := by
    rw [← pow_mul, show 5 * 3 = 15 by norm_num]
    exact hgp15
  have hωne : ¬((g : GaloisField 2 4) ^ 5 = 1) := by
    intro h
    have h' : g ^ 5 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)
    have hdvd : 15 ∣ 5 := by
      have h2 := (orderOf_dvd_iff_pow_eq_one).symm.mp h'
      rw [hord] at h2
      exact h2
    omega
  have hω : ((g : GaloisField 2 4) ^ 5) ^ 2 + (g : GaloisField 2 4) ^ 5 + 1 = 0 := by
    have hexpand : ∀ x : GaloisField 2 4,
        (x - 1) * (x ^ 2 + x + 1) = x ^ 3 - 1 := by intro x; ring
    have hfac : ((g : GaloisField 2 4) ^ 5 - 1) *
        (((g : GaloisField 2 4) ^ 5) ^ 2 + (g : GaloisField 2 4) ^ 5 + 1) = 0 := by
      rw [hexpand, hω3]
      ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h (sub_ne_zero.mpr hωne)
    · exact h
  have h2M : (1 : GaloisField 2 4) + 1 = 0 := by
    have hchar : (2 : GaloisField 2 4) = 0 := CharP.cast_eq_zero (R := GaloisField 2 4) 2
    linear_combination hchar
  have h01M : (0 : GaloisField 2 4) ≠ 1 := zero_ne_one
  have hcard : Nat.card (ZMod 31 × GaloisField 2 4) = 496 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, hcardK]
    try norm_num
  obtain ⟨hE677, a, b, c, hcol, hne⟩ :=
    FiniteMagmaE677.magma496_generic ((g : GaloisField 2 4) ^ 3)
      ((g : GaloisField 2 4) ^ 5) hζ hω h2M h01M
  refine ⟨ZMod 31 × GaloisField 2 4, inferInstance,
    FiniteMagmaE677.magma496 ((g : GaloisField 2 4) ^ 3) ((g : GaloisField 2 4) ^ 5),
    hcard, hE677, ?_⟩
  intro hrc
  exact hne (hrc a b c hcol)

theorem solution :
    ∃ (α : Type) (_ : Fintype α) (op : α → α → α),
      Nat.card α = 496 ∧ FiniteMagmaE677.E677 op ∧
      ¬(∀ a b c : α, op a c = op b c → a = b) :=
  FiniteMagmaE677.exists_e677_not_right_cancellable_496
