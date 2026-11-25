-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.aLoc_eq_roL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:04.013356+00:00
-- url     : https://prove2.me/submissions/def6e1f9-2547-46f6-9287-43b6724839dc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_exists_vF_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_valF_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_alphaN_eq_of_vF_eq


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
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (h𝔭 : 𝔭 ∉ S) {n : 𝓞 F} (hn : n ≠ 0) :
    aLoc h L 𝔭 n = roL h L S 𝔭 (valF n 𝔭) := by
  have hv : vd h L 𝔭.1 = 0 := by
    by_contra hne
    exact h𝔭 (hS 𝔭 hne)
  obtain ⟨hn', hvn'⟩ := (exists_vF_eq 𝔭.2 (valF n 𝔭)).choose_spec
  rw [roL, if_neg h𝔭]
  unfold aLoc
  rw [alphaN_eq_of_vF_eq hK hF hs hd hL hLi 𝔭.2 hv hn hn' (by rw [hvn', valF_apply hn])]
end Formalism.HermitianLattices.Ext.L3.A5
