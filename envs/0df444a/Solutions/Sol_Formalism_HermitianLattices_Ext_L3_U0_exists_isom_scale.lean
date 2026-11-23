-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_isom_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:44.943914+00:00
-- url     : https://prove2.me/submissions/20c4750c-b324-43e4-ad92-b713563619dd

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
theorem _root_.solution (hs : h.IsSymm) {z : V} (hz : h z z ≠ 0) {b : K} (hb : star b * b = 1) :
    ∃ ψ ∈ Formalism.HermitianLatticesTheory.isom h, ψ z = b • z ∧ ∀ v, h z v = 0 → ψ v = v := by
  have hN : starRingEnd K (h z z) = h z z := hs.eq z z
  have hNi : h z z * (h z z)⁻¹ = 1 := mul_inv_cancel₀ hz
  have hz0 : ∀ (v : V) (c : K), c = 0 → v + c • z = v := fun v c hc => by
    rw [hc, zero_smul, add_zero]
  let f : V →ₗ[K] V :=
    LinearMap.id + (LinearMap.toSpanSingleton K V z) ∘ₗ (((b - 1) * (h z z)⁻¹) • h z)
  let f' : V →ₗ[K] V :=
    LinearMap.id + (LinearMap.toSpanSingleton K V z) ∘ₗ (((star b - 1) * (h z z)⁻¹) • h z)
  have hf : ∀ v, f v = v + ((b - 1) * (h z z)⁻¹ * h z v) • z := fun v => by simp [f]
  have hf' : ∀ v, f' v = v + ((star b - 1) * (h z z)⁻¹ * h z v) • z := fun v => by simp [f']
  have c1 : f ∘ₗ f' = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_add, map_smul, smul_eq_mul, add_assoc,
      ← add_smul]
    apply hz0
    linear_combination ((h z z)⁻¹ * h z v) * hb +
      ((h z z)⁻¹ * h z v * (b - 1) * (star b - 1)) * hNi
  have c2 : f' ∘ₗ f = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_add, map_smul, smul_eq_mul, add_assoc,
      ← add_smul]
    apply hz0
    linear_combination ((h z z)⁻¹ * h z v) * hb +
      ((h z z)⁻¹ * h z v * (b - 1) * (star b - 1)) * hNi
  refine ⟨LinearEquiv.ofLinear f f' c1 c2, fun a c => ?_, ?_, fun v hv => ?_⟩
  · change h (f a) (f c) = h a c
    rw [hf a, hf c]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.smul_apply,
      smul_eq_mul, map_mul, map_inv₀, map_sub, map_one, hN]
    rw [← hs.eq z a]
    simp only [starRingEnd_apply]
    linear_combination ((h z z)⁻¹ * star (h z a) * h z c) * hb +
      ((h z z)⁻¹ * star (h z a) * h z c * (b - 1) * (star b - 1)) * hNi
  · change f z = b • z
    rw [hf, mul_assoc, inv_mul_cancel₀ hz, mul_one, sub_smul, one_smul]
    abel
  · change f v = v
    rw [hf, hv, mul_zero, zero_smul, add_zero]
end Formalism.HermitianLattices.Ext.L3.U0
