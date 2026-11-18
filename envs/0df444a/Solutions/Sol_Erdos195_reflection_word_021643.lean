-- Prove2me | solution 1 for Erdos195.reflection_word_021643
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-17T16:30:25.905677+00:00
-- url     : https://prove2.me/submissions/5c565437-e00e-4fbd-8c30-fa4a9953dac7

import Definitions.Def_Erdos195_tree
import Theorems.Thm_Erdos195_exists_treeLt_safe_iff
import Mathlib.Data.List.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Erdos195

private def Qw : List ℤ := [0, 2, 1, 6, 4, 3]

private lemma mem_Qw {a : ℤ} :
    a ∈ Qw ↔ a = 0 ∨ a = 2 ∨ a = 1 ∨ a = 6 ∨ a = 4 ∨ a = 3 := by
  simp [Qw]

private lemma continuation_Qw :
    ∀ a b : ℤ, a ∈ Qw → b ∈ Qw → 2 * b - a ∈ Qw → Qw.idxOf a < Qw.idxOf b →
      Qw.idxOf b < Qw.idxOf (2 * b - a) →
      3 * b - 2 * a ∈ Qw ∧ Qw.idxOf (3 * b - 2 * a) < Qw.idxOf (2 * b - a) := by
  intro a b ha hb
  rcases mem_Qw.mp ha with ha | ha | ha | ha | ha | ha <;> subst ha <;>
    rcases mem_Qw.mp hb with hb | hb | hb | hb | hb | hb <;> subst hb <;>
    decide

private lemma open_pairs_Qw {a b : ℤ}
    (ha : a ∈ Qw) (hb : b ∈ Qw)
    (hord : Qw.idxOf a < Qw.idxOf b)
    (h2 : 2 * b - a ∉ Qw) (h3 : 3 * b - 2 * a ∉ Qw) :
    (a = 0 ∧ b = 6) ∨ (a = 0 ∧ b = 4) ∨ (a = 2 ∧ b = 6) ∨
    (a = 1 ∧ b = 6) ∨ (a = 1 ∧ b = 4) ∨ (a = 1 ∧ b = 3) := by
  rcases mem_Qw.mp ha with ha | ha | ha | ha | ha | ha <;> subst ha <;>
    rcases mem_Qw.mp hb with hb | hb | hb | hb | hb | hb <;> subst hb <;>
    first | decide | tauto

private lemma instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private lemma pv2_of_odd {n : ℤ} (h : n % 2 = 1) : padicValInt 2 n = 0 := by
  have : ¬ (2 : ℤ) ∣ n := by
    intro hd
    have : n % 2 = 0 := Int.emod_eq_zero_of_dvd hd
    omega
  exact padicValInt.eq_zero_of_not_dvd this

private lemma pv2_two : padicValInt 2 (2 : ℤ) = 1 := by
  haveI := instPrimeTwo
  exact padicValInt_self (p := 2)

private lemma pv2_mul_odd {m : ℤ} (hm : m % 2 = 1) (hne : m ≠ 0) :
    padicValInt 2 (2 * m) = 1 := by
  haveI := instPrimeTwo
  have hmul := padicValInt.mul (p := 2) (a := (2 : ℤ)) (b := m) (by decide) hne
  rw [hmul, pv2_two, pv2_of_odd hm]

private lemma pv2_four : padicValInt 2 (4 : ℤ) = 2 := by
  haveI := instPrimeTwo
  have h : (4 : ℤ) = 2 * 2 := by decide
  have hmul := padicValInt.mul (p := 2) (a := (2 : ℤ)) (b := (2 : ℤ)) (by decide) (by decide)
  rw [h, hmul, pv2_two]

private lemma pv2_six : padicValInt 2 (6 : ℤ) = 1 := pv2_mul_odd (m := 3) (by decide) (by decide)

private lemma no_conflict_Qw :
    ∀ a b a' b' : ℤ,
      a ∈ Qw → b ∈ Qw → Qw.idxOf a < Qw.idxOf b →
      2 * b - a ∉ Qw → 3 * b - 2 * a ∉ Qw →
      a' ∈ Qw → b' ∈ Qw → Qw.idxOf a' < Qw.idxOf b' →
      2 * b' - a' ∉ Qw → 3 * b' - 2 * a' ∉ Qw →
      padicValInt 2 (b - a) = padicValInt 2 (b' - a') →
      a % 2 ^ padicValInt 2 (b - a) = a' % 2 ^ padicValInt 2 (b - a) →
      (bitOne b (padicValInt 2 (b - a)) ↔ bitOne b' (padicValInt 2 (b - a))) := by
  intro a b a' b' ha hb hord h2 h3 ha' hb' hord' h2' h3' hval hres
  have hp := open_pairs_Qw ha hb hord h2 h3
  have hp' := open_pairs_Qw ha' hb' hord' h2' h3'
  have pv5 : padicValInt 2 (5 : ℤ) = 0 := pv2_of_odd (by decide)
  have pv3 : padicValInt 2 (3 : ℤ) = 0 := pv2_of_odd (by decide)
  have pv1 : padicValInt 2 (1 : ℤ) = 0 := pv2_of_odd (by decide)
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    try exact Iff.rfl
  all_goals
    try simp [pv2_six, pv2_four, pv2_two, pv5, pv3, pv1] at hval hres ⊢
  all_goals
    first
    | exact Iff.rfl
    | (exfalso; omega)
    | decide

private lemma release_Qw :
    ∀ a b : ℤ, a ∈ Qw → b ∈ Qw → Qw.idxOf a < Qw.idxOf b →
      2 * b - a ∉ Qw → 3 * b - 2 * a ∉ Qw → (b - a) % 2 = 1 → b % 2 = 0 := by
  intro a b ha hb hord h2 h3
  have hp := open_pairs_Qw ha hb hord h2 h3
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    decide

theorem reflection_word_021643 :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 2, 1, 6, 4, 3]) ∧
    (∀ a b : ℤ, a ∈ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      b ∈ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      [0, 2, 1, 6, 4, 3].idxOf a < [0, 2, 1, 6, 4, 3].idxOf b →
      2 * b - a ∉ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      3 * b - 2 * a ∉ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      (b - a) % 2 = 1 → b % 2 = 0) := by
  constructor
  · rw [exists_treeLt_safe_iff]
    exact ⟨continuation_Qw, no_conflict_Qw⟩
  · simpa [Qw] using release_Qw

end Erdos195

theorem solution :
    (∃ θ : ℕ → ℤ → Bool, Erdos195.Safe (Erdos195.treeLt θ) [0, 2, 1, 6, 4, 3]) ∧
    (∀ a b : ℤ, a ∈ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      b ∈ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      [0, 2, 1, 6, 4, 3].idxOf a < [0, 2, 1, 6, 4, 3].idxOf b →
      2 * b - a ∉ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      3 * b - 2 * a ∉ ([0, 2, 1, 6, 4, 3] : List ℤ) →
      (b - a) % 2 = 1 → b % 2 = 0) :=
  Erdos195.reflection_word_021643
