-- Prove2me | solution 1 for Chou.hasPackingProperty_int
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:10:21.861681+00:00
-- url     : https://prove2.me/submissions/39415566-0b33-41dd-9268-6b92baf04163

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

/-! # Chou §2: Propositions 2.1 and 2.2

`Constructible` is closed under subgroups and quotients (one structural induction proving both at
once — Chou's transfinite induction), hence coincides with `ElementaryAmenable`. -/

universe u

namespace Chou
namespace Lib

open Subgroup QuotientGroup

end Lib
end Chou

/-! # Chou §2: Theorem 2.3 and Corollary 2.4 -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Small tools -/

/-! ### Locally finite groups -/

/-! ### Periodic groups lie in NF; NF ∖ EG is nonempty -/

/-! ### Corollary 2.4 -/

end Lib
end Chou

/-! # Chou §4: packings and property (P) — the basic cases and Lemmas 4.1, 4.6 (a) -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Packings -/

lemma isPacking_iff {G : Type*} [Group G] (S X : Set G) :
    IsPacking S X ↔ (∀ s ∈ S, ∀ x ∈ X, ∀ s' ∈ S, ∀ x' ∈ X, s * x = s' * x' → s = s' ∧ x = x') ∧
      (∀ g : G, ∃ s ∈ S, ∃ x ∈ X, s * x = g) := by
  constructor
  · rintro ⟨-, hinj, hsurj⟩
    refine ⟨fun s hs x hx s' hs' x' hx' h => ?_, fun g => ?_⟩
    · have := @hinj (s, x) ⟨hs, hx⟩ (s', x') ⟨hs', hx'⟩ h
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    · obtain ⟨⟨s, x⟩, ⟨hs, hx⟩, h⟩ := hsurj (Set.mem_univ g)
      exact ⟨s, hs, x, hx, h⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · rintro ⟨s, x⟩ ⟨hs, hx⟩ ⟨s', x'⟩ ⟨hs', hx'⟩ h
      obtain ⟨rfl, rfl⟩ := hinj s hs x hx s' hs' x' hx' h
      rfl
    · intro g _
      obtain ⟨s, hs, x, hx, h⟩ := hsurj g
      exact ⟨(s, x), ⟨hs, hx⟩, h⟩

/-! ### Finite groups and the integers -/

theorem hasPackingProperty_int' : HasPackingProperty (Multiplicative ℤ) := by
  intro F hF
  -- a bound `n` with `|toAdd f| ≤ n` on `F`
  obtain ⟨n, hn⟩ : ∃ n : ℤ, 0 ≤ n ∧ ∀ f ∈ F, |Multiplicative.toAdd f| ≤ n := by
    obtain ⟨b, hb⟩ := (hF.image (fun f => |Multiplicative.toAdd f|)).bddAbove
    exact ⟨max b 0, le_max_right _ _, fun f hf => (hb ⟨f, hf, rfl⟩).trans (le_max_left _ _)⟩
  set m : ℤ := 2 * n + 1 with hm
  have hmpos : 0 < m := by omega
  refine ⟨{s | |Multiplicative.toAdd s| ≤ n}, Set.range (fun k : ℤ => Multiplicative.ofAdd (m * k)),
    fun f hf => hn.2 f hf, ?_, (isPacking_iff _ _).mpr ⟨?_, ?_⟩⟩
  · -- the box is finite: it is the image of `Icc (-n) n`
    have : {s : Multiplicative ℤ | |Multiplicative.toAdd s| ≤ n}
        ⊆ Multiplicative.ofAdd '' Set.Icc (-n) n := by
      intro s hs
      exact ⟨Multiplicative.toAdd s, abs_le.mp hs, rfl⟩
    exact (Set.finite_Icc _ _).image _ |>.subset this
  · rintro s hs _ ⟨k, rfl⟩ s' hs' _ ⟨k', rfl⟩ h
    simp only [Set.mem_setOf_eq] at hs hs'
    have h' : Multiplicative.toAdd s + m * k = Multiplicative.toAdd s' + m * k' := by
      have := congrArg Multiplicative.toAdd h
      rwa [toAdd_mul, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd] at this
    have hdvd : m ∣ Multiplicative.toAdd s' - Multiplicative.toAdd s :=
      ⟨k - k', by linear_combination -h'⟩
    have hzero : Multiplicative.toAdd s' - Multiplicative.toAdd s = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hdvd
      have := abs_le.mp hs; have := abs_le.mp hs'
      rw [abs_lt]; constructor <;> omega
    have hs_eq : s = s' := by
      apply Multiplicative.toAdd.injective; omega
    subst hs_eq
    have hk : k = k' := by
      have : m * k = m * k' := by omega
      exact mul_left_cancel₀ hmpos.ne' this
    exact ⟨rfl, by rw [hk]⟩
  · intro g
    set a := Multiplicative.toAdd g with ha
    refine ⟨Multiplicative.ofAdd ((a + n) % m - n), ?_, Multiplicative.ofAdd (m * ((a + n) / m)),
      ⟨(a + n) / m, rfl⟩, ?_⟩
    · show |(a + n) % m - n| ≤ n
      have h1 := Int.emod_nonneg (a + n) hmpos.ne'
      have h2 := Int.emod_lt_of_pos (a + n) hmpos
      rw [abs_le]; constructor <;> omega
    · apply Multiplicative.toAdd.injective
      have := Int.emod_add_ediv_mul (a + n) m
      simp only [toAdd_mul, toAdd_ofAdd, ha]
      linear_combination this

/-! ### Lemma 4.1 (a): directed unions -/

end Lib
end Chou

open Chou

theorem solution : HasPackingProperty (Multiplicative ℤ) :=
  Chou.Lib.hasPackingProperty_int'
