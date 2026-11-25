-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.singS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:53:10.124688+00:00
-- url     : https://prove2.me/submissions/83d1af01-3942-4702-8ff0-a3307c3f9948

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_aLoc_eq_roL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_roL_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_prod_aLoc

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
theorem _root_.solution {n : 𝓞 F} (hn : n ≠ 0) :
    singS F h L n = (∏ 𝔭 ∈ S, aLoc h L 𝔭 n) * (valF n).prod (roL h L S) := by
  classical
  have hz : ∀ 𝔭, roL h L S 𝔭 0 = 1 := fun 𝔭 => roL_zero (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hm := hm) (hS := hS) 𝔭
  have e1 : singS F h L n = ∏' 𝔭, aLoc h L 𝔭 n := rfl
  have hsup : (valF n).support ⊆ S ∪ (valF n).support := Finset.subset_union_right
  rw [e1, tprod_eq_prod (s := S ∪ (valF n).support) ?_,
    prod_aLoc (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) Finset.subset_union_left hn,
    Finsupp.prod_of_support_subset _ hsup _ (fun 𝔭 _ => hz 𝔭)]
  intro 𝔭 h𝔭
  rw [Finset.mem_union, not_or] at h𝔭
  have h0 : valF n 𝔭 = 0 := by
    by_contra hne
    exact h𝔭.2 (Finsupp.mem_support_iff.mpr hne)
  rw [aLoc_eq_roL (hK := hK) (hF := hF) (hs := hs) (hd := hd) (hL := hL) (hLi := hLi) (hS := hS) h𝔭.1 hn, h0, hz]
end Formalism.HermitianLattices.Ext.L3.A5
