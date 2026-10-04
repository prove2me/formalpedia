-- Prove2me | solution 1 for Garrido.satisfiesInvariantExtensionTheorem_of_isAmenable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T22:51:53.236544+00:00
-- url     : https://prove2.me/submissions/27721167-8802-419f-9deb-7b9eabab7164

import Definitions.Def_Garrido_Amenability
import Definitions.Def_Garrido_BooleanExtension
import Theorems.Thm_Garrido_exists_invariant_extension_of_isSetRing
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
# The Stone representation is equivariant

A group acting on a boolean algebra `A` by order automorphisms acts on its Stone space `Pt A`
(`Stone.act`), and `rep (ρ g a) = g • rep a`.
-/

open scoped Pointwise

namespace Garrido.Stone

section Action

variable {A : Type*} [BooleanAlgebra A]

lemma orderIso_compl (e : A ≃o A) (a : A) : e aᶜ = (e a)ᶜ :=
  ((e.isCompl isCompl_compl).compl_eq).symm

/-- The preimage of an ultrafilter under an order automorphism is an ultrafilter. -/
lemma isUltra_preimage (e : A ≃o A) (U : Pt A) : IsUltra {a : A | e a ∈ U.1} := by
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · simp only [Set.mem_setOf_eq, OrderIso.map_inf]
    exact mem_inf U _ _
  · simp only [Set.mem_setOf_eq, orderIso_compl]
    exact mem_compl U _

variable {G : Type*} [Group G]

/-- The action of `G` on the Stone space induced by an action on `A`:
`g • U = {a | ρ g⁻¹ a ∈ U} = ρ g '' U`. -/
@[reducible] def act (ρ : G →* (A ≃o A)) : MulAction G (Pt A) where
  smul g U := ⟨{a : A | ρ g⁻¹ a ∈ U.1}, isUltra_preimage (ρ g⁻¹) U⟩
  one_smul U := by
    apply Subtype.ext
    show {a : A | ρ 1⁻¹ a ∈ U.1} = U.1
    ext a
    simp
  mul_smul g h U := by
    apply Subtype.ext
    show {a : A | ρ (g * h)⁻¹ a ∈ U.1} = {a : A | ρ g⁻¹ a ∈ {b : A | ρ h⁻¹ b ∈ U.1}}
    ext a
    simp only [Set.mem_setOf_eq, mul_inv_rev, map_mul, RelIso.coe_mul, Function.comp_apply]

/-- Equivariance of the Stone representation. -/
lemma smul_rep (ρ : G →* (A ≃o A)) (g : G) (a : A) :
    (letI := act ρ; g • rep a) = rep (ρ g a) := by
  let _ := act ρ
  ext V
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [rep, Set.mem_setOf_eq]
  change a ∈ {b : A | ρ g⁻¹⁻¹ b ∈ V.1} ↔ _
  simp

end Action

end Garrido.Stone

end
end

section
section
/-!
# Garrido, Theorem 2.6 for every boolean algebra

`G` acts on the Stone space `Pt A` of `A` (`Stone.act`), the Stone representation `rep` is
equivariant, the image `rep '' R` of an invariant subring is an invariant ring of sets, and the
transported measure is invariant on it. The power-set theorem
`Garrido.exists_invariant_extension_of_isSetRing` gives an invariant extension to all subsets of
`Pt A`, which pulls back along `rep`.
-/

open scoped ENNReal Pointwise

namespace Garrido

theorem satisfiesInvariantExtensionTheorem_of_isAmenable {G : Type*} [Group G]
    (hG : IsAmenable G) : SatisfiesInvariantExtensionTheorem G := by
  intro A _ ρ R hR hRinv μ hμ hμinv
  let _ : MulAction G (Stone.Pt A) := Stone.act ρ
  have hRinv' : ∀ (g : G), ∀ s ∈ Stone.rep '' R, g • s ∈ Stone.rep '' R := by
    rintro g _ ⟨r, hr, rfl⟩
    rw [Stone.smul_rep]
    exact ⟨ρ g r, hRinv g r hr, rfl⟩
  have hμinv' : ∀ (g : G), ∀ s ∈ Stone.rep '' R,
      Stone.transport μ (g • s) = Stone.transport μ s := by
    rintro g _ ⟨r, hr, rfl⟩
    rw [Stone.smul_rep, Stone.transport_rep, Stone.transport_rep]
    exact hμinv g r hr
  obtain ⟨ν, ⟨hν0, hνadd⟩, hνR, hνinv⟩ := exists_invariant_extension_of_isSetRing hG
    (Stone.isSetRing_image hR) hRinv' (Stone.transport μ) (Stone.transport_empty hμ.1)
    (Stone.transport_add hμ) hμinv'
  refine ⟨fun a => ν (Stone.rep a), Stone.isFinitelyAdditiveOn_univ_comp hν0 hνadd, ?_, ?_⟩
  · intro r hr
    show ν (Stone.rep r) = μ r
    rw [hνR _ ⟨r, hr, rfl⟩, Stone.transport_rep]
  · intro g a
    show ν (Stone.rep (ρ g a)) = ν (Stone.rep a)
    rw [← Stone.smul_rep]
    exact hνinv g _

end Garrido

end
end

section
open Garrido

theorem solution {G : Type*} [Group G]
    (hG : IsAmenable G) : SatisfiesInvariantExtensionTheorem G := by
  apply Garrido.satisfiesInvariantExtensionTheorem_of_isAmenable <;> assumption

end
