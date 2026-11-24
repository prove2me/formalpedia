-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.val_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:31.472856+00:00
-- url     : https://prove2.me/submissions/f5d6316c-9539-4cf9-b2e4-40673616dd2d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_star_mem_extP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_comap_extP_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_form_mem_right
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (𝔭 : Ideal (𝓞 F)) (k : ℕ) {y y' : ↥L} {n n' : 𝓞 F}
    (hy : y - y' ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L))
    (e : h (y : V) (y : V) = algebraMap F K (n : F))
    (e' : h (y' : V) (y' : V) = algebraMap F K (n' : F)) : n - n' ∈ 𝔭 ^ k := by
  obtain ⟨z1, hz1, e1⟩ := form_mem_right hLi 𝔭 k y' hy
  obtain ⟨z2, hz2, e2⟩ := form_mem_right hLi 𝔭 k (y - y') hy
  obtain ⟨z3, hz3, e3⟩ := star_mem_extP hF 𝔭 k hz1
  rw [← comap_extP_pow (K := K), Ideal.mem_comap]
  have : algebraMap (𝓞 F) (𝓞 K) (n - n') = z1 + z2 + z3 := by
    apply RingOfIntegers.coe_injective
    have h3 : star (h (y' : V) ((y - y' : ↥L) : V)) = h ((y - y' : ↥L) : V) (y' : V) := hs.eq _ _
    rw [algebraMap_comp, map_add, map_add, e1, e2, e3, e1, h3]
    have : algebraMap F K ((n - n' : 𝓞 F) : F) = algebraMap F K (n : F) - algebraMap F K (n' : F) := by
      simp
    rw [this, ← e, ← e']
    simp only [Submodule.coe_sub, map_sub, LinearMap.sub_apply]
    ring
  rw [this]
  exact add_mem (add_mem hz1 hz2) hz3
end Formalism.HermitianLattices.Ext.L3.MeanB
