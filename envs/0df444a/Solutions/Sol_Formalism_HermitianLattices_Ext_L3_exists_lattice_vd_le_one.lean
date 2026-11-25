-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_lattice_vd_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:00:35.584205+00:00
-- url     : https://prove2.me/submissions/c0b7b591-dea2-499a-847d-cb8204c95f05

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdLeOneOfBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
private theorem algebraMap_int_F_to_K_eq_algebraMap_F_K (n : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := by
  rw [← IsScalarTower.algebraMap_apply]
  first
  | exact IsScalarTower.algebraMap_apply (𝓞 F) F K n
  | (rw [IsScalarTower.algebraMap_apply (𝓞 F) F K]; rfl)
  | simp
end Formalism.HermitianLattices.Ext.L3
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} {n : 𝓞 F} (hx : h x₀ x₀ = algebraMap F K (n : F)) (hn : n ∉ 𝔭) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
      x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
  exact Cell.exists_lattice (𝔭 := 𝔭) hK hF hs hd h𝔭 (by rw [algebraMap_int_F_to_K_eq_algebraMap_F_K]; exact hx) hn
end Formalism.HermitianLattices.Ext.L3
