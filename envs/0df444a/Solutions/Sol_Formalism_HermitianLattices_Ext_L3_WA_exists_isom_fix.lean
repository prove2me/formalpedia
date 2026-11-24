-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.exists_isom_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:42.298873+00:00
-- url     : https://prove2.me/submissions/fd962973-d3ce-41ed-a55a-17db68d04d5c

import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_quasiRefl_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_quasiRefl_comp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_quasiRefl_isom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    {x y : V} (hx : h x x = 1) (hy : h y y = 1) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ ∀ v, h x v = 0 → h y v = 0 → τ v = v := by
  have hsym : ∀ p q : V, star (h p q) = h q p := fun p q => by
    have := hs.eq p q
    simpa [starRingEnd_apply] using this
  by_cases hyx : h y x = 1
  · have hxy : h x y = 1 := by rw [← hsym, hyx, star_one]
    have hu : h (x - y) (x - y) = 0 := by
      simp only [map_sub, LinearMap.sub_apply, hx, hy, hxy, hyx]; ring
    have hxy' : x = y := sub_eq_zero.mp (hd _ hu)
    subst hxy'
    exact ⟨1, one_mem _, rfl, fun v _ _ => rfl⟩
  · have hp : (1 : K) - h y x ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
    have hq : (1 : K) - h x y ≠ 0 := by
      intro h0
      apply hp
      have := congrArg star h0
      rw [star_sub, star_one, hsym, star_zero] at this
      exact this
    have huu : h (x - y) (x - y) = (1 - h y x) + (1 - h x y) := by
      simp only [map_sub, LinearMap.sub_apply, hx, hy]; ring
    have hux : h (x - y) x = 1 - h y x := by
      simp only [map_sub, LinearMap.sub_apply, hx]
    have hsa : star ((1 - h y x)⁻¹) = (1 - h x y)⁻¹ := by
      first
      | rw [star_inv₀, star_sub, star_one, hsym]
      | rw [star_inv', star_sub, star_one, hsym]
    have e1 : (1 - h y x)⁻¹ * (1 - h y x) = 1 := inv_mul_cancel₀ hp
    have e2 : (1 - h x y)⁻¹ * (1 - h x y) = 1 := inv_mul_cancel₀ hq
    have ha : (1 - h y x)⁻¹ + star ((1 - h y x)⁻¹) =
        (1 - h y x)⁻¹ * star ((1 - h y x)⁻¹) * h (x - y) (x - y) := by
      rw [hsa, huu]
      linear_combination (-(1 - h x y)⁻¹) * e1 - (1 - h y x)⁻¹ * e2
    have hb : star ((1 - h y x)⁻¹) + (1 - h y x)⁻¹ =
        star ((1 - h y x)⁻¹) * (1 - h y x)⁻¹ * h (x - y) (x - y) := by
      rw [add_comm, mul_comm (star _) _]; exact ha
    refine ⟨LinearEquiv.ofLinear (quasiRefl h (x - y) ((1 - h y x)⁻¹))
      (quasiRefl h (x - y) (star ((1 - h y x)⁻¹))) (quasiRefl_comp h (x - y) ha)
      (quasiRefl_comp h (x - y) hb), ?_, ?_, ?_⟩
    · first
      | exact fun v w => quasiRefl_isom hs (x - y) ha v w
      | (intro v w; exact quasiRefl_isom hs (x - y) ha v w)
      | (show ∀ v w, _ = _; intro v w; exact quasiRefl_isom hs (x - y) ha v w)
    · show quasiRefl h (x - y) ((1 - h y x)⁻¹) x = y
      rw [quasiRefl_apply, hux, inv_mul_cancel₀ hp, one_smul, sub_sub_cancel]
    · intro v h1 h2
      show quasiRefl h (x - y) ((1 - h y x)⁻¹) v = v
      rw [quasiRefl_apply, map_sub, LinearMap.sub_apply, h1, h2, sub_zero, mul_zero, zero_smul, sub_zero]
end Formalism.HermitianLattices.Ext.L3.WA
