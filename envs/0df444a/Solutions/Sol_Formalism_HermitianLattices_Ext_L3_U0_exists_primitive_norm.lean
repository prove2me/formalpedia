-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_primitive_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:45.430089+00:00
-- url     : https://prove2.me/submissions/734e3df3-69dd-4742-af4d-0e57d583ad7d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_primitive
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_mul_mem


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
theorem _root_.solution (hS : IsHermSemilocal S) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsLatIn S h W M) {ξ : V} (hξ : ξ ∈ W) {u : K} (hu : IsUnitIn S u) (hξu : h ξ ξ = u) :
    ∃ y ∈ M, y ≠ 0 ∧ (∃ l : K, y = l • ξ) ∧ (∀ c : K, c • y ∈ M → c ∈ S) ∧
      ∃ a ∈ S, h y y = star a * a * u := by
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hu.1
    rw [← hξu]
    simp
  obtain ⟨l, hl0, hlM, hl⟩ := exists_primitive hS hd hM hξ hξ0
  have hyy : h (l • ξ) (l • ξ) = star l * l * u := by
    simp only [LinearMap.map_smulₛₗ₂, map_smul, starRingEnd_apply, smul_eq_mul, hξu]
    ring
  have hN : star l * l ∈ S := by
    have h1 := hM.int _ hlM _ hlM
    rw [hyy] at h1
    have h2 := S.mul_mem h1 hu.2.2
    rwa [mul_assoc, mul_inv_cancel₀ hu.1, mul_one] at h2
  obtain ⟨b, hb1, hbS⟩ := WA.exists_norm_one_mul_mem hS hN
  refine ⟨l • ξ, hlM, smul_ne_zero hl0 hξ0, ⟨l, rfl⟩, fun c hc => ?_, l * b, hbS, ?_⟩
  · have h1 := hl (c * l) (by rwa [mul_smul])
    rwa [mul_assoc, mul_inv_cancel₀ hl0, mul_one] at h1
  · rw [hyy, star_mul]
    calc star l * l * u = star l * l * (star b * b) * u := by rw [hb1, mul_one]
      _ = star b * star l * (l * b) * u := by ring
end Formalism.HermitianLattices.Ext.L3.U0
