-- Prove2me | solution 1 for Garrido.exists_extension_of_isBooleanSubring
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T22:51:53.345985+00:00
-- url     : https://prove2.me/submissions/7e225c20-0770-4ee8-9144-ddae1c8a82ff

import Definitions.Def_Garrido_BooleanExtension
import Theorems.Thm_FinitelyAdditive_exists_extension_of_isSetRing
import Mathlib


section
section
/-!
# A Stone representation of a boolean algebra

For a boolean algebra `A`, the points `Pt A` are the ultrafilters of `A`, encoded as the sets
`U ⊆ A` with `a ⊓ b ∈ U ↔ a ∈ U ∧ b ∈ U` and `aᶜ ∈ U ↔ a ∉ U`. The map `rep a = {U | a ∈ U}`
sends `⊥, ⊔, ⊓, \` to `∅, ∪, ∩, \` and is injective (the prime ideal theorem,
`DistribLattice.prime_ideal_of_disjoint_filter_ideal`).
-/

namespace Garrido.Stone

section Basic

variable {A : Type*} [BooleanAlgebra A]

/-- An ultrafilter of a boolean algebra, as a set. -/
def IsUltra (U : Set A) : Prop :=
  (∀ a b : A, a ⊓ b ∈ U ↔ a ∈ U ∧ b ∈ U) ∧ ∀ a : A, aᶜ ∈ U ↔ a ∉ U

variable (A) in
/-- The Stone space of `A`, as a type (no topology). -/
def Pt : Type _ := {U : Set A // IsUltra U}

/-- The Stone representation. -/
def rep (a : A) : Set (Pt A) := {U | a ∈ U.1}

lemma mem_inf (U : Pt A) (a b : A) : a ⊓ b ∈ U.1 ↔ a ∈ U.1 ∧ b ∈ U.1 := U.2.1 a b

lemma mem_compl (U : Pt A) (a : A) : aᶜ ∈ U.1 ↔ a ∉ U.1 := U.2.2 a

lemma bot_notMem (U : Pt A) : (⊥ : A) ∉ U.1 := by
  intro h
  have h1 : (⊥ : A) ⊓ (⊥ : A)ᶜ ∈ U.1 := by simpa using h
  exact (mem_compl U ⊥).1 ((mem_inf U _ _).1 h1).2 h

lemma mem_sup (U : Pt A) (a b : A) : a ⊔ b ∈ U.1 ↔ a ∈ U.1 ∨ b ∈ U.1 := by
  have e : a ⊔ b = (aᶜ ⊓ bᶜ)ᶜ := by simp [compl_inf]
  rw [e, mem_compl, mem_inf, mem_compl, mem_compl]
  tauto

lemma mem_sdiff (U : Pt A) (a b : A) : a \ b ∈ U.1 ↔ a ∈ U.1 ∧ b ∉ U.1 := by
  rw [sdiff_eq, mem_inf, mem_compl]

lemma rep_bot : rep (⊥ : A) = ∅ := by
  ext U
  simp only [rep, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact bot_notMem U

lemma rep_sup (a b : A) : rep (a ⊔ b) = rep a ∪ rep b := by
  ext U
  simp only [rep, Set.mem_setOf_eq, Set.mem_union]
  exact mem_sup U a b

lemma rep_inf (a b : A) : rep (a ⊓ b) = rep a ∩ rep b := by
  ext U
  simp only [rep, Set.mem_setOf_eq, Set.mem_inter_iff]
  exact mem_inf U a b

lemma rep_sdiff (a b : A) : rep (a \ b) = rep a \ rep b := by
  ext U
  simp only [rep, Set.mem_setOf_eq, Set.mem_diff]
  exact mem_sdiff U a b

/-- Every nonzero element lies in an ultrafilter (the prime ideal theorem). -/
lemma exists_mem_of_ne_bot {c : A} (hc : c ≠ ⊥) : ∃ U : Pt A, c ∈ U.1 := by
  have hdisj : Disjoint ((Order.PFilter.principal c : Order.PFilter A) : Set A)
      ((Order.Ideal.principal (⊥ : A) : Order.Ideal A) : Set A) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : c ≤ x := Order.PFilter.mem_principal.1 hx
    have h2 : x ≤ ⊥ := Order.Ideal.mem_principal.1 hx'
    exact hc (le_bot_iff.1 (h1.trans h2))
  obtain ⟨J, hJ, -, hFJ⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hdisj
  refine ⟨⟨(J : Set A)ᶜ, ?_, ?_⟩, ?_⟩
  · intro a b
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · intro h
      exact ⟨fun ha => h (J.lower inf_le_left ha), fun hb => h (J.lower inf_le_right hb)⟩
    · rintro ⟨ha, hb⟩ hab
      rcases hJ.mem_or_mem hab with h | h
      · exact ha h
      · exact hb h
  · intro a
    simp only [Set.mem_compl_iff, SetLike.mem_coe, not_not]
    constructor
    · intro h
      exact (hJ.mem_or_compl_mem).resolve_right h
    · intro ha hac
      apply hJ.toIsProper.top_notMem
      have : a ⊔ aᶜ ∈ J := Order.Ideal.sup_mem ha hac
      simpa using this
  · have hc' : c ∈ ((Order.PFilter.principal c : Order.PFilter A) : Set A) :=
      Order.PFilter.mem_principal.2 le_rfl
    exact Set.disjoint_left.1 hFJ hc'

lemma rep_eq_empty_iff (c : A) : rep c = ∅ ↔ c = ⊥ := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨U, hU⟩ := exists_mem_of_ne_bot hc
    have : U ∈ rep c := hU
    rw [h] at this
    exact this
  · rintro rfl
    exact rep_bot

lemma rep_injective : Function.Injective (rep : A → Set (Pt A)) := by
  intro a b h
  have h1 : rep (a \ b) = ∅ := by rw [rep_sdiff, h, Set.diff_self]
  have h2 : rep (b \ a) = ∅ := by rw [rep_sdiff, h, Set.diff_self]
  rw [rep_eq_empty_iff, sdiff_eq_bot_iff] at h1 h2
  exact le_antisymm h1 h2

lemma disjoint_rep_iff (a b : A) : Disjoint (rep a) (rep b) ↔ Disjoint a b := by
  rw [Set.disjoint_iff_inter_eq_empty, ← rep_inf, rep_eq_empty_iff, disjoint_iff]

end Basic


end Garrido.Stone

end
end

section
section
/-!
# Measures along the Stone representation

A subring of `A` goes to a ring of sets under `rep`; a finitely additive measure on the subring is
transported to `rep '' R`, and a finitely additive measure on all subsets of `Pt A` pulls back to a
finitely additive measure on all of `A`.
-/

open scoped ENNReal

namespace Garrido

namespace Stone

variable {A : Type*} [BooleanAlgebra A]

/-- The image of a subring is a ring of sets. -/
lemma isSetRing_image {R : Set A} (hR : IsBooleanSubring R) :
    MeasureTheory.IsSetRing (rep '' R) where
  empty_mem := ⟨⊥, hR.1, rep_bot⟩
  union_mem := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ⊔ b, (hR.2 a ha b hb).1, rep_sup a b⟩
  sdiff_mem := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a \ b, (hR.2 a ha b hb).2, rep_sdiff a b⟩

/-- The measure transported to subsets of the Stone space. -/
noncomputable def transport (μ : A → ℝ≥0∞) : Set (Pt A) → ℝ≥0∞ :=
  haveI : Nonempty A := ⟨⊥⟩
  fun S => μ (Function.invFun rep S)

lemma transport_rep (μ : A → ℝ≥0∞) (a : A) : transport μ (rep a) = μ a := by
  have : Nonempty A := ⟨⊥⟩
  unfold transport
  rw [Function.leftInverse_invFun rep_injective a]

lemma transport_empty {μ : A → ℝ≥0∞} (h0 : μ ⊥ = 0) : transport μ ∅ = 0 := by
  rw [← rep_bot, transport_rep, h0]

lemma transport_add {R : Set A} {μ : A → ℝ≥0∞}
    (hμ : IsFinitelyAdditiveOn R μ) :
    ∀ s ∈ rep '' R, ∀ t ∈ rep '' R, Disjoint s t →
      transport μ (s ∪ t) = transport μ s + transport μ t := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hst
  rw [← rep_sup, transport_rep, transport_rep, transport_rep]
  exact hμ.2 a ha b hb ((disjoint_rep_iff a b).1 hst)

/-- Pulling a finitely additive measure on all subsets of `Pt A` back along `rep`. -/
lemma isFinitelyAdditiveOn_univ_comp {ν : Set (Pt A) → ℝ≥0∞} (hν0 : ν ∅ = 0)
    (hνadd : ∀ s t : Set (Pt A), Disjoint s t → ν (s ∪ t) = ν s + ν t) :
    IsFinitelyAdditiveOn (Set.univ : Set A) (fun a => ν (rep a)) := by
  refine ⟨?_, ?_⟩
  · show ν (rep ⊥) = 0
    rw [rep_bot, hν0]
  · intro a _ b _ hab
    show ν (rep (a ⊔ b)) = ν (rep a) + ν (rep b)
    rw [rep_sup]
    exact hνadd _ _ ((disjoint_rep_iff a b).2 hab)

end Stone

end Garrido

end
end

section
section
/-!
# The recalled Carathéodory extension for a subring of a boolean algebra (Garrido, Theorem 2.6)

Transport the measure along the Stone representation `rep : A → Set (Pt A)` to the ring of sets
`rep '' R`, extend it to all subsets of `Pt A` with `FinitelyAdditive.exists_extension_of_isSetRing`,
and pull the extension back along `rep`.
-/

open scoped ENNReal

namespace Garrido


theorem exists_extension_of_isBooleanSubring {A : Type*} [BooleanAlgebra A] (R : Set A)
    (hR : IsBooleanSubring R) (μ : A → ENNReal) (hμ : IsFinitelyAdditiveOn R μ) :
    ∃ μbar : A → ENNReal, IsFinitelyAdditiveOn Set.univ μbar ∧ ∀ r ∈ R, μbar r = μ r := by
  obtain ⟨ν, hν0, hνadd, hνR⟩ := FinitelyAdditive.exists_extension_of_isSetRing
    (Stone.isSetRing_image hR) (Stone.transport μ) (Stone.transport_empty hμ.1)
    (Stone.transport_add hμ)
  refine ⟨fun a => ν (Stone.rep a), Stone.isFinitelyAdditiveOn_univ_comp hν0 hνadd, ?_⟩
  intro r hr
  show ν (Stone.rep r) = μ r
  rw [hνR _ ⟨r, hr, rfl⟩, Stone.transport_rep]

end Garrido

end
end

section
open Garrido

theorem solution {A : Type*} [BooleanAlgebra A] (R : Set A)
    (hR : IsBooleanSubring R) (μ : A → ENNReal) (hμ : IsFinitelyAdditiveOn R μ) :
    ∃ μbar : A → ENNReal, IsFinitelyAdditiveOn Set.univ μbar ∧ ∀ r ∈ R, μbar r = μ r := by
  apply Garrido.exists_extension_of_isBooleanSubring <;> assumption

end
