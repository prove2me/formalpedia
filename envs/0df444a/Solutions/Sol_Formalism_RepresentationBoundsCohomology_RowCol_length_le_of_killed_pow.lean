-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.RowCol.length_le_of_killed_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:36.105818+00:00
-- url     : https://prove2.me/submissions/684ec1b3-5ba3-4234-97b6-011076c9dccf

import Definitions.Def_Formalism_WachLatticeTwists_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_RowCol_length_le_of_killed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.RowCol
open Module
namespace Formalism.RepresentationBoundsCohomology.RowCol
theorem _root_.solution {O : Type*} [CommRing O] (b : O) : ∀ (e : ℕ) {X : Type*}
    [AddCommGroup X] [Module O X] {ι : Type*} [Fintype ι] (g : (ι → O) →ₗ[O] X),
    Function.Surjective g → (∀ x : X, b ^ e • x = 0) →
    Module.length O X ≤
      (e : ℕ∞) * ((Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {b})) := by
  intro e
  induction e with
  | zero =>
    intro X _ _ ι _ g _ hb
    have : Subsingleton X := ⟨fun x y => by
      have hx := hb x
      have hy := hb y
      simp only [pow_zero, one_smul] at hx hy
      rw [hx, hy]⟩
    rw [Module.length_eq_zero_iff.mpr this]
    exact zero_le
  | succ e ih =>
    intro X _ _ ι _ g hg hb
    let φ : X →ₗ[O] X := b • LinearMap.id
    let Y : Submodule O X := LinearMap.range φ
    have hlen := Module.length_eq_add_of_exact Y.subtype Y.mkQ Y.injective_subtype Y.mkQ_surjective
      (LinearMap.exact_subtype_mkQ Y)
    let gY : (ι → O) →ₗ[O] Y := φ.rangeRestrict.comp g
    have hgY : Function.Surjective gY := (LinearMap.surjective_rangeRestrict φ).comp hg
    have hbY : ∀ y : Y, b ^ e • y = 0 := by
      intro y
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      rw [← hx]
      show b ^ e • (b • x) = 0
      rw [smul_smul, ← pow_succ]
      exact hb x
    have hY := ih gY hgY hbY
    have hbQ : ∀ z : X ⧸ Y, b • z = 0 := by
      intro z
      obtain ⟨x, rfl⟩ := Y.mkQ_surjective z
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range.mpr ⟨x, rfl⟩
    have hQ := length_le_of_killed b (Y.mkQ.comp g) (Y.mkQ_surjective.comp hg) hbQ
    rw [hlen]
    calc _ ≤ (e : ℕ∞) * ((Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {b})) +
          (Fintype.card ι : ℕ∞) * Module.length O (O ⧸ Ideal.span {b}) := add_le_add hY hQ
      _ = _ := by push_cast; ring
end Formalism.RepresentationBoundsCohomology.RowCol
