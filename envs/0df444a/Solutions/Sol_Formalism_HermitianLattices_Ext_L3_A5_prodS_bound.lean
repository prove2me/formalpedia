-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.prodS_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:46:03.070707+00:00
-- url     : https://prove2.me/submissions/cd275266-f395-44db-a430-1135bec6968b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_alphaN_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_eFac_pos


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
omit hS
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ C : ℝ, ∀ n : 𝓞 F, n ≠ 0 →
      0 ≤ ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ∧ ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ≤ C := by
  have hm1 : 1 ≤ finrank K V := by omega
  choose C hC using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    alphaN_bound hK hF hs hd hL hLi hm 𝔭.2
  refine ⟨∏ 𝔭 ∈ S, C 𝔭 / eFac K (finrank K V) 𝔭.1, fun n hn => ?_⟩
  have hpos : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 0 < eFac K (finrank K V) 𝔭.1 :=
    fun 𝔭 => eFac_pos 𝔭.2 hm1
  have h0 : ∀ 𝔭 ∈ S, 0 ≤ aLoc h L 𝔭 n := fun 𝔭 _ => div_nonneg (hC 𝔭 n hn).1 (hpos 𝔭).le
  refine ⟨Finset.prod_nonneg h0, Finset.prod_le_prod h0 fun 𝔭 _ => ?_⟩
  exact div_le_div_of_nonneg_right (hC 𝔭 n hn).2 (hpos 𝔭).le
end Formalism.HermitianLattices.Ext.L3.A5
