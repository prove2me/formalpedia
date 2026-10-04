-- Prove2me | solution 1 for Garrido.isAmenable_tfae_satisfiesInvariantExtensionTheorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T22:51:53.325979+00:00
-- url     : https://prove2.me/submissions/cc1348a1-6c3d-4cef-afda-a2c6814deef6

import Definitions.Def_Garrido_Amenability
import Definitions.Def_Garrido_BooleanExtension
import Definitions.Def_Garrido_Equidecomposability
import Theorems.Thm_Garrido_isAmenable_tfae
import Theorems.Thm_Garrido_satisfiesInvariantExtensionTheorem_of_isAmenable
import Mathlib

universe u v

section
section
/-!
# Garrido, Theorem 2.7 as printed

(1) ⇔ (2) ⇔ (3) is `Garrido.isAmenable_tfae`; (1) ⇒ (4) is Theorem 2.6
(`Garrido.satisfiesInvariantExtensionTheorem_of_isAmenable`); (4) ⇒ (1) applies the Invariant
Extension Theorem to the boolean algebra of all subsets of `ULift G` (in `Type (max u v)`), the
subring `{∅, univ}`, the measure that is `1` on `univ` and `0` on `∅`, and left translation; the
invariant extension, read on `G`, is the measure witnessing amenability.
-/

open scoped ENNReal Pointwise


namespace Garrido

namespace TFAE

variable {G : Type u} [Group G]

/-- Left translation on `ULift G`, as a permutation. -/
def lperm (g : G) : Equiv.Perm (ULift.{v} G) :=
  Equiv.ulift.trans ((Equiv.mulLeft g).trans Equiv.ulift.symm)

@[simp] lemma lperm_apply (g : G) (x : ULift.{v} G) : lperm g x = ULift.up (g * x.down) := rfl

/-- The action of `G` on the boolean algebra of subsets of `ULift G` by left translation. -/
def lact : G →* (Set (ULift.{v} G) ≃o Set (ULift.{v} G)) where
  toFun g := (lperm g).toOrderIsoSet
  map_one' := by
    ext s x
    simp [lperm]
  map_mul' g h := by
    ext s x
    simp only [Equiv.toOrderIsoSet_apply, RelIso.coe_mul, Function.comp_apply, Set.mem_image,
      lperm_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ULift.up (h * y.down), ⟨y, hy, rfl⟩, by simp [mul_assoc]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [mul_assoc]⟩

@[simp] lemma lact_apply (g : G) (s : Set (ULift.{v} G)) :
    lact g s = (lperm g) '' s := rfl

lemma lact_empty (g : G) : lact.{u, v} g ∅ = ∅ := by simp

lemma lact_univ (g : G) : lact.{u, v} g Set.univ = Set.univ := by
  simp [Set.image_univ_of_surjective (lperm g).surjective]

lemma isAmenable_of_satisfiesInvariantExtensionTheorem
    (h : SatisfiesInvariantExtensionTheorem.{u, v} G) : IsAmenable G := by
  classical
  let R : Set (Set (ULift.{v} G)) := {∅, Set.univ}
  have hne : (∅ : Set (ULift.{v} G)) ≠ Set.univ := fun h0 => by
    have : ULift.up (1 : G) ∈ (∅ : Set (ULift.{v} G)) := h0 ▸ Set.mem_univ _
    exact this
  let μ : Set (ULift.{v} G) → ℝ≥0∞ := fun s => if s = Set.univ then 1 else 0
  have hμ0 : μ ∅ = 0 := by simp [μ, hne]
  have hμ1 : μ Set.univ = 1 := by simp [μ]
  have hR : IsBooleanSubring R := by
    refine ⟨Or.inl rfl, ?_⟩
    rintro a (rfl | rfl) b (rfl | rfl) <;> simp [R]
  have hRinv : ∀ (g : G), ∀ r ∈ R, lact g r ∈ R := by
    rintro g r (rfl | rfl)
    · rw [lact_empty]; exact Or.inl rfl
    · rw [lact_univ]; exact Or.inr rfl
  have hμ : IsFinitelyAdditiveOn R μ := by
    refine ⟨hμ0, ?_⟩
    rintro a (rfl | rfl) b (rfl | rfl) hab
    · simp [hμ0]
    · simp [hμ0]
    · simp [hμ0]
    · exfalso
      simp at hab
  have hμinv : ∀ (g : G), ∀ r ∈ R, μ (lact g r) = μ r := by
    rintro g r (rfl | rfl)
    · rw [lact_empty]
    · rw [lact_univ]
  obtain ⟨μbar, ⟨hb0, hbadd⟩, hbR, hbinv⟩ :=
    h (Set (ULift.{v} G)) lact R hR hRinv μ hμ hμinv
  refine ⟨fun s => μbar (ULift.down ⁻¹' s), ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa using hb0
  · intro s t hst
    show μbar (ULift.down ⁻¹' (s ∪ t)) = μbar (ULift.down ⁻¹' s) + μbar (ULift.down ⁻¹' t)
    rw [Set.preimage_union]
    exact hbadd _ trivial _ trivial (hst.preimage _)
  · show μbar (ULift.down ⁻¹' Set.univ) = 1
    rw [Set.preimage_univ, hbR _ (Or.inr rfl), hμ1]
  · intro g s
    show μbar (ULift.down ⁻¹' (g • s)) = μbar (ULift.down ⁻¹' s)
    have e : ULift.down ⁻¹' (g • s) = lact g (ULift.down ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage, lact_apply, Set.mem_image, lperm_apply]
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      constructor
      · intro hx
        exact ⟨ULift.up (g⁻¹ * x.down), hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [e]
    exact hbinv g _

end TFAE

theorem isAmenable_tfae_satisfiesInvariantExtensionTheorem (G : Type*) [Group G] :
    [IsAmenable G,
      HasInvariantMean G,
      ¬ IsParadoxical G (Set.univ : Set G),
      SatisfiesInvariantExtensionTheorem G].TFAE := by
  have h3 := isAmenable_tfae G
  tfae_have 1 → 4 := satisfiesInvariantExtensionTheorem_of_isAmenable
  tfae_have 4 → 1 := TFAE.isAmenable_of_satisfiesInvariantExtensionTheorem
  tfae_have 1 ↔ 2 := h3.out 0 1
  tfae_have 1 ↔ 3 := h3.out 0 2
  tfae_finish

end Garrido

end
end

section
open Garrido

theorem solution (G : Type*) [Group G] :
    [IsAmenable G,
      HasInvariantMean G,
      ¬ IsParadoxical G (Set.univ : Set G),
      SatisfiesInvariantExtensionTheorem G].TFAE := by
  apply Garrido.isAmenable_tfae_satisfiesInvariantExtensionTheorem <;> assumption

end
