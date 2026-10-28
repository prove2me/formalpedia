-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteTapePrefixBound.prefix_mass_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:25:44.838818+00:00
-- url     : https://prove2.me/submissions/5b57578e-5ffc-4807-878c-e1bfeb2aa720

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_append_event_ncard

section


set_option autoImplicit false

/-!
Finite fair-bit conditioning by a consumed prefix. Appending a fixed prefix
is a bijection on its suffix event; disjoint consumed-prefix cylinders let
uniform suffix estimates transfer to the whole finite tape. This module
proves only counting facts, not the program's stopping-prefix property or
the phase's conditional analytic estimate.
-/

namespace CountingMatroid.Analysis.FiniteTapePrefixBound

/-- INTERNAL: There are exactly `2^m` Boolean tapes of length `m`.
TEXLINE: main.tex:1392-1421 -/
theorem fair_lists_ncard (m : ℕ) :
    Set.ncard {bits : List Bool | bits.length = m} = 2 ^ m := by
  change Nat.card (List.Vector Bool m) = _
  rw [Nat.card_eq_fintype_card, card_vector]
  simp



/-- INTERNAL: A fixed-prefix event has prefix mass times its fresh-suffix
mass under the finite uniform fair-bit law. This is the conditional-law
identity used before applying a uniform estimate for each successful history.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem append_event_mass (m : ℕ) (pref : List Bool)
    (hlen : pref.length ≤ m) (E : List Bool → Prop) :
    (Set.ncard {bits : List Bool | bits.length = m ∧ pref <+: bits ∧ E bits} :
      ENNReal) * (1 / 2 : ENNReal) ^ m =
    (1 / 2 : ENNReal) ^ pref.length *
      ((Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
        E (pref ++ suffix)} : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length)) := by
  rw [append_event_ncard m pref hlen E]
  have hp : (1 / 2 : ENNReal) ^ m =
      (1 / 2 : ENNReal) ^ pref.length * (1 / 2 : ENNReal) ^ (m - pref.length) := by
    rw [← Nat.add_sub_of_le hlen, pow_add]
    simp only [Nat.add_sub_cancel_left]
  rw [hp]
  ac_rfl



/-- INTERNAL: Prefix-free consumed histories define disjoint tape cylinders.
TEXLINE: main.tex:1207-1212 -/
theorem prefix_cylinder_disjoint (m : ℕ) (P : Finset (List Bool))
    (hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b) :
    (P : Set (List Bool)).PairwiseDisjoint
      (fun pref => {bits : List Bool | bits.length = m ∧ pref <+: bits}) := by
  intro a ha b hb hab
  apply Set.disjoint_left.mpr
  intro bits hba hbb
  rcases List.prefix_or_prefix_of_prefix hba.2 hbb.2 with h | h
  · exact hab (hfree a ha b hb h)
  · exact hab (hfree b hb a ha h).symm





end CountingMatroid.Analysis.FiniteTapePrefixBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r19 · proved · Boolean tape count, fixed-prefix event bijection and mass, stopping-prefix freeness, prefix-cylinder disjointness, total prefix mass bound, and transfer of uniform suffix bounds. These counting results are used by `FiniteTapeLowerTail`; actual successful-history replay and analytic phase bounds are separate obligations.
-/

end
set_option autoImplicit false

/-!
Finite fair-bit conditioning by a consumed prefix. Appending a fixed prefix
is a bijection on its suffix event; disjoint consumed-prefix cylinders let
uniform suffix estimates transfer to the whole finite tape. This module
proves only counting facts, not the program's stopping-prefix property or
the phase's conditional analytic estimate.
-/

namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteTapePrefixBound

/-- INTERNAL: Prefix-free histories consume total fair-bit mass at most one,
even when their consumed lengths differ.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem solution (m : ℕ) (P : Finset (List Bool))
    (hlen : ∀ pref ∈ P, pref.length ≤ m)
    (hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b) :
    ∑ pref ∈ P, (1 / 2 : ENNReal) ^ pref.length ≤ 1 := by
  classical
  let cylinder := fun pref => {bits : List Bool | bits.length = m ∧ pref <+: bits}
  have hfinite (pref : List Bool) : (cylinder pref).Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  have hcard : (⋃ pref ∈ P, cylinder pref).ncard =
      ∑ pref ∈ P, (cylinder pref).ncard := by
    have hc := P.finite_toSet.ncard_biUnion (fun pref _ => hfinite pref)
      (prefix_cylinder_disjoint m P hfree)
    calc
      _ = ∑ᶠ pref ∈ (P : Set (List Bool)), (cylinder pref).ncard := hc
      _ = _ := finsum_mem_coe_finset (fun pref => (cylinder pref).ncard) P
  have hbound : (⋃ pref ∈ P, cylinder pref).ncard ≤ 2 ^ m := by
    rw [← fair_lists_ncard m]
    apply Set.ncard_le_ncard _ (List.finite_length_eq Bool m)
    intro bits hb
    obtain ⟨pref, hb⟩ := Set.mem_iUnion.mp hb
    obtain ⟨_, hb⟩ := Set.mem_iUnion.mp hb
    exact hb.1
  have htwo : (2 : ENNReal) * (1 / 2) = 1 := by
    rw [div_eq_mul_inv, one_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
  have hmass (pref : List Bool) (hp : pref ∈ P) :
      ((cylinder pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m =
        (1 / 2 : ENNReal) ^ pref.length := by
    have hc := append_event_mass m pref (hlen pref hp) (fun _ => True)
    simp only [and_true, fair_lists_ncard, Nat.cast_pow, Nat.cast_ofNat] at hc
    change ((cylinder pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m = _ at hc
    rw [← mul_pow, htwo,
      one_pow, mul_one] at hc
    exact hc
  calc
    ∑ pref ∈ P, (1 / 2 : ENNReal) ^ pref.length =
        ∑ pref ∈ P, ((cylinder pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := by
      apply Finset.sum_congr rfl
      intro pref hp
      exact (hmass pref hp).symm
    _ = ((⋃ pref ∈ P, cylinder pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := by
      rw [hcard, Nat.cast_sum, Finset.sum_mul]
    _ ≤ ((2 ^ m : ℕ) : ENNReal) * (1 / 2 : ENNReal) ^ m := by gcongr
    _ = 1 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
      rw [htwo, one_pow]
