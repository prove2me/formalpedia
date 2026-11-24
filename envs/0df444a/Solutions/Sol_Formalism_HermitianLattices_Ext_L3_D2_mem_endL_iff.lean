-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.mem_endL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:53:01.212925+00:00
-- url     : https://prove2.me/submissions/50f2d11c-ddf1-4dbf-83b5-8ac6eb33a6f6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_basis_mem_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_repr_mem_pK_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_span_iff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_smul_mem_smul
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (D : V →ₗ[K] V) :
    D ∈ endL (locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)))
        (extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a))) ↔
      ∀ i j, LinearMap.toMatrix a a D i j ∈ pK K 𝔭 k := by
  constructor
  · intro hD i j
    rw [LinearMap.toMatrix_apply]
    exact (mem_smul_span_iff a h𝔭 k _).1 (hD _ (basis_mem_locF a 𝔭 j)) i
  · intro hD x hx
    rw [← a.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    have h1 : D (a j) ∈ extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) :=
      (mem_smul_span_iff a h𝔭 k _).2 fun i => by
        rw [← LinearMap.toMatrix_apply]
        exact hD i j
    simpa using smul_mem_smul h𝔭 _ (repr_mem_pK_zero a h𝔭 hx j) h1
end Formalism.HermitianLattices.Ext.L3.D2
