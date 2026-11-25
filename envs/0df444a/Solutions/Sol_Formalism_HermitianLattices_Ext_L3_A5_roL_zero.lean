-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.roL_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:10.312593+00:00
-- url     : https://prove2.me/submissions/01c7dc05-3f4e-40f0-a5cb-b0e92674f60e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_eFac_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_exists_vF_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_alphaN_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mem_pow_iff_le_vF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
  {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
  (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
  {S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}}
  (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S)
include hK hF hs hd hL hLi hS
include hm
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) : roL h L S 𝔭 0 = 1 := by
  by_cases h𝔭 : 𝔭 ∈ S
  · rw [roL, if_pos h𝔭]
  · have hv : vd h L 𝔭.1 = 0 := by
      by_contra hne
      exact h𝔭 (hS 𝔭 hne)
    obtain ⟨hn', hvn'⟩ := (exists_vF_eq 𝔭.2 0).choose_spec
    have hn𝔭 : (exists_vF_eq 𝔭.2 0).choose ∉ 𝔭.1 := by
      intro hmem
      have := (mem_pow_iff_le_vF 𝔭.2 hn' 1).mp (by rw [pow_one]; exact hmem)
      omega
    rw [roL, if_neg h𝔭]
    unfold aLoc
    rw [unitaryAbsoluteValueBounds.alphaN_unit hK hF hs hd hL hLi 𝔭.2 hv (by omega) hn𝔭]
    have he := eFac_pos (K := K) 𝔭.2 (m := finrank K V) (by omega)
    unfold eFac at he ⊢
    exact div_self he.ne'
end Formalism.HermitianLattices.Ext.L3.A5
