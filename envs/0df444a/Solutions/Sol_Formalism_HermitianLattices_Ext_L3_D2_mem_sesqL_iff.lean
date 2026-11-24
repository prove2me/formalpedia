-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_sesqL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:52:02.420383+00:00
-- url     : https://prove2.me/submissions/39a5a1ec-717b-489c-97a4-94c1d2449764

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_basis_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_repr_mem_pK_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mul_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_star_mem_pK


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hF : IsFixF K F) {κ : Type} [Fintype κ] (a : Basis κ K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (s : V →ₗ⋆[K] V →ₗ[K] K) :
    s ∈ sesqL (locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) 𝔭 k ↔
      ∀ i j, s (a i) (a j) ∈ pK K 𝔭 k := by
  constructor
  · intro hs i j
    exact hs _ (basis_mem_locF a 𝔭 i) _ (basis_mem_locF a 𝔭 j)
  · intro hs x hx y hy
    rw [← a.sum_repr x, ← a.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    have h1 := mul_mem_pK h𝔭 (repr_mem_pK_zero a h𝔭 hy j)
      (mul_mem_pK h𝔭 (star_mem_pK hF h𝔭 (repr_mem_pK_zero a h𝔭 hx i)) (hs i j))
    rw [zero_add, zero_add] at h1
    exact h1
end Formalism.HermitianLattices.Ext.L3.D2
