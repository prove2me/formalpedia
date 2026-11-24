-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_isom_move
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:46.802798+00:00
-- url     : https://prove2.me/submissions/002245ba-e3d1-4dc9-936e-0e7c47bc5293

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomScale
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {x y : V}
    (hxy : h x x = h y y) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by
  by_cases hxy' : x = y
  · subst hxy'
    exact ⟨1, one_mem _, rfl, fun v _ _ => rfl, fun W _ _ v => Iff.rfl⟩
  generalize hu_def : x - y = u
  have hD : h u u = h u x + starRingEnd K (h u x) := by
    rw [hs.eq u x, ← hu_def]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hxy]
    ring
  have hu0 : u ≠ 0 := by rw [← hu_def]; exact sub_ne_zero.2 hxy'
  have hD0 : h u x ≠ 0 := by
    intro e
    apply hu0
    apply hd
    rw [hD, e, map_zero, add_zero]
  have hD0' : starRingEnd K (h u x) ≠ 0 := by rwa [map_ne_zero]
  let f : V →ₗ[K] V := LinearMap.id - (LinearMap.toSpanSingleton K V u) ∘ₗ ((h u x)⁻¹ • h u)
  let f' : V →ₗ[K] V :=
    LinearMap.id - (LinearMap.toSpanSingleton K V u) ∘ₗ ((starRingEnd K (h u x))⁻¹ • h u)
  have hf : ∀ v, f v = v - ((h u x)⁻¹ * h u v) • u := fun v => by simp [f]
  have hf' : ∀ v, f' v = v - ((starRingEnd K (h u x))⁻¹ * h u v) • u := fun v => by simp [f']
  have c1 : f ∘ₗ f' = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_sub, map_smul, smul_eq_mul, sub_sub,
      ← add_smul, sub_eq_self]
    apply smul_eq_zero_of_left
    rw [hD]
    field_simp
    ring
  have c2 : f' ∘ₗ f = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_sub, map_smul, smul_eq_mul, sub_sub,
      ← add_smul, sub_eq_self]
    apply smul_eq_zero_of_left
    rw [hD]
    field_simp
    ring
  refine ⟨LinearEquiv.ofLinear f f' c1 c2, fun a b => ?_, ?_, fun v hxv hyv => ?_, fun W hxW hyW v => ?_⟩
  · change h (f a) (f b) = h a b
    rw [hf a, hf b]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.smul_apply,
      smul_eq_mul, map_mul, map_inv₀]
    rw [← hs.eq u a, hD]
    field_simp
    ring
  · change f x = y
    rw [hf, inv_mul_cancel₀ hD0, one_smul, ← hu_def, sub_sub_cancel]
  · change f v = v
    have huv : h u v = 0 := by rw [← hu_def, LinearMap.map_sub₂, hxv, hyv, sub_zero]
    rw [hf, huv, mul_zero, zero_smul, sub_zero]
  · have huW : u ∈ W := by rw [← hu_def]; exact W.sub_mem hxW hyW
    change v ∈ W ↔ f v ∈ W
    rw [hf]
    exact (Submodule.sub_mem_iff_left W (W.smul_mem _ huW)).symm
end Formalism.HermitianLattices.Ext.L3.U0
