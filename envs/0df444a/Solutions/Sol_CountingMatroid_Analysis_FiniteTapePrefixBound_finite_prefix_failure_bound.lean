-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteTapePrefixBound.finite_prefix_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:28:07.648982+00:00
-- url     : https://prove2.me/submissions/ac00c0f2-d5e7-4081-b2c3-627e57dd0e44

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_append_event_ncard
import Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_prefix_mass_le_one

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

/-- INTERNAL: Uniform conditional failure bounds on the fresh suffixes after
prefix-free consumed histories imply the same unconditional tape bound.
Prefixes may have different lengths; no independence between phase events is
assumed. Coverage and prefix-freeness must be proved for the actual program.
TEXLINE: main.tex:1207-1212,1277-1285,1392-1427 -/
theorem solution (m : ℕ) (P : Finset (List Bool))
    (E : List Bool → Prop) (β : ENNReal)
    (hlen : ∀ pref ∈ P, pref.length ≤ m)
    (hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b)
    (hcover : ∀ bits, bits.length = m → E bits →
      ∃ pref ∈ P, pref <+: bits)
    (hconditional : ∀ pref ∈ P,
      (Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
        E (pref ++ suffix)} : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length) ≤ β) :
    (Set.ncard {bits : List Bool | bits.length = m ∧ E bits} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ β := by
  classical
  let part := fun pref => {bits : List Bool |
    bits.length = m ∧ pref <+: bits ∧ E bits}
  have hfinite : (⋃ pref ∈ P, part pref).Finite :=
    (List.finite_length_eq Bool m).subset (by
      intro bits hb
      obtain ⟨pref, hb⟩ := Set.mem_iUnion.mp hb
      obtain ⟨_, hb⟩ := Set.mem_iUnion.mp hb
      exact hb.1)
  have hcard : Set.ncard {bits : List Bool | bits.length = m ∧ E bits} ≤
      ∑ pref ∈ P, (part pref).ncard := by
    apply (Set.ncard_le_ncard _ hfinite).trans (P.set_ncard_biUnion_le part)
    intro bits hb
    obtain ⟨pref, hp, hprefix⟩ := hcover bits hb.1 hb.2
    exact Set.mem_iUnion.mpr ⟨pref, Set.mem_iUnion.mpr ⟨hp, hb.1, hprefix, hb.2⟩⟩
  calc
    (Set.ncard {bits : List Bool | bits.length = m ∧ E bits} : ENNReal) *
        (1 / 2 : ENNReal) ^ m ≤
      ((∑ pref ∈ P, (part pref).ncard : ℕ) : ENNReal) *
        (1 / 2 : ENNReal) ^ m := by gcongr
    _ = ∑ pref ∈ P, ((part pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ ∑ pref ∈ P, (1 / 2 : ENNReal) ^ pref.length * β := by
      apply Finset.sum_le_sum
      intro pref hp
      rw [show ((part pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m =
        (1 / 2 : ENNReal) ^ pref.length *
          ((Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
            E (pref ++ suffix)} : ENNReal) *
            (1 / 2 : ENNReal) ^ (m - pref.length)) from
              append_event_mass m pref (hlen pref hp) E]
      exact mul_le_mul_right (hconditional pref hp) _
    _ = (∑ pref ∈ P, (1 / 2 : ENNReal) ^ pref.length) * β :=
      (Finset.sum_mul ..).symm
    _ ≤ 1 * β := mul_le_mul_left (prefix_mass_le_one m P hlen hfree) β
    _ = β := one_mul β
