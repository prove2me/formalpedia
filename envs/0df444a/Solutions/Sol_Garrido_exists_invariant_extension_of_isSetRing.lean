-- Prove2me | solution 1 for Garrido.exists_invariant_extension_of_isSetRing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T23:16:05.126551+00:00
-- url     : https://prove2.me/submissions/cf75e0fd-194a-4cb3-b741-313c3200b716

import Mathlib
import Definitions.Def_Garrido_Amenability
import Theorems.Thm_FinitelyAdditive_exists_extension_of_isSetRing
import Theorems.Thm_Garrido_hasInvariantExtensionProperty_of_isAmenable

/-!
# Garrido, Theorem 2.6 for power sets, with `X` in any universe

The published statement takes `X : Type (max u v)`; a `solution` stated with that binder leaves
the verifier a stuck universe constraint `max ?a ?b =?= max ?c ?d` (submission 73e73819, WA).
Here `X : Type w` is independent, so the verifier's unification sets `w := max u v`. The proof
extends `μ` with `FinitelyAdditive.exists_extension_of_isSetRing`, moves everything to
`ULift.{u} X : Type (max w u)`, where `Garrido.hasInvariantExtensionProperty_of_isAmenable`
applies, and pulls the invariant extension back along `ULift.down`.
-/

open scoped Pointwise ENNReal

universe u w

namespace Garrido

theorem exists_invariant_extension_of_isSetRing_ulift {G : Type u} [Group G]
    (hG : IsAmenable G) {X : Type w} [MulAction G X] {R : Set (Set X)}
    (hR : MeasureTheory.IsSetRing R)
    (hRinv : ∀ (g : G), ∀ s ∈ R, g • s ∈ R) (μ : Set X → ENNReal) (h0 : μ ∅ = 0)
    (hadd : ∀ s ∈ R, ∀ t ∈ R, Disjoint s t → μ (s ∪ t) = μ s + μ t)
    (hμinv : ∀ (g : G), ∀ s ∈ R, μ (g • s) = μ s) :
    ∃ μbar : Set X → ENNReal, IsFinitelyAdditiveMeasure μbar ∧ (∀ s ∈ R, μbar s = μ s) ∧
      IsInvariant G μbar := by
  obtain ⟨ν, hν0, hνadd, hνR⟩ := FinitelyAdditive.exists_extension_of_isSetRing hR μ h0 hadd
  -- the lifted set of `s`
  let L : Set X → Set (ULift.{u} X) := fun s => ULift.down ⁻¹' s
  have hL : ∀ s : Set X, ULift.up ⁻¹' L s = s := fun s => rfl
  have hLsmul : ∀ (g : G) (s : Set X), g • L s = L (g • s) := by
    intro g s
    ext y
    simp only [L, Set.mem_preimage]
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
    rfl
  let R' : Set (Set (ULift.{u} X)) := L '' R
  let μ' : Set (ULift.{u} X) → ℝ≥0∞ := fun S => μ (ULift.up ⁻¹' S)
  let ν' : Set (ULift.{u} X) → ℝ≥0∞ := fun S => ν (ULift.up ⁻¹' S)
  have hR'inv : ∀ (g : G) (S : Set (ULift.{u} X)), S ∈ R' → g • S ∈ R' := by
    rintro g _ ⟨s, hs, rfl⟩
    rw [hLsmul]
    exact ⟨g • s, hRinv g s hs, rfl⟩
  have hμ'inv : ∀ (g : G) (S : Set (ULift.{u} X)), S ∈ R' → μ' (g • S) = μ' S := by
    rintro g _ ⟨s, hs, rfl⟩
    show μ (ULift.up ⁻¹' (g • L s)) = μ (ULift.up ⁻¹' L s)
    rw [hLsmul, hL, hL]
    exact hμinv g s hs
  have hν'R : ∀ S ∈ R', ν' S = μ' S := by
    rintro _ ⟨s, hs, rfl⟩
    exact hνR s hs
  have hν' : IsFinitelyAdditiveMeasure ν' := by
    refine ⟨hν0, fun S T hST => ?_⟩
    show ν (ULift.up ⁻¹' (S ∪ T)) = ν (ULift.up ⁻¹' S) + ν (ULift.up ⁻¹' T)
    rw [Set.preimage_union]
    exact hνadd _ _ (hST.preimage _)
  obtain ⟨m, ⟨hm0, hmadd⟩, hmR, hminv⟩ :=
    hasInvariantExtensionProperty_of_isAmenable.{u, w} hG (ULift.{u} X) R' μ' ν'
      hR'inv hμ'inv hν'R hν'
  refine ⟨fun s => m (L s), ⟨?_, ?_⟩, ?_, ?_⟩
  · exact hm0
  · intro s t hst
    show m (L (s ∪ t)) = m (L s) + m (L t)
    exact hmadd _ _ (hst.preimage _)
  · intro s hs
    show m (L s) = μ s
    rw [hmR _ ⟨s, hs, rfl⟩]
    rfl
  · intro g s
    show m (L (g • s)) = m (L s)
    rw [← hLsmul]
    exact hminv g _

end Garrido

section
open Garrido
open scoped Pointwise

/-- The published statement with `X` in its own universe `w`: the verifier's unification then sets
`w := max u v` instead of meeting `max ?a ?b =?= max ?c ?d`. -/
theorem solution {G : Type u} [Group G] (hG : IsAmenable G)
    {X : Type w} [MulAction G X] {R : Set (Set X)} (hR : MeasureTheory.IsSetRing R)
    (hRinv : ∀ (g : G), ∀ s ∈ R, g • s ∈ R) (μ : Set X → ENNReal) (h0 : μ ∅ = 0)
    (hadd : ∀ s ∈ R, ∀ t ∈ R, Disjoint s t → μ (s ∪ t) = μ s + μ t)
    (hμinv : ∀ (g : G), ∀ s ∈ R, μ (g • s) = μ s) :
    ∃ μbar : Set X → ENNReal, IsFinitelyAdditiveMeasure μbar ∧ (∀ s ∈ R, μbar s = μ s) ∧
      IsInvariant G μbar :=
  exists_invariant_extension_of_isSetRing_ulift hG hR hRinv μ h0 hadd hμinv

end
