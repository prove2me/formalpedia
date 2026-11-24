-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.alphaL_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:58:08.206859+00:00
-- url     : https://prove2.me/submissions/0c6e2d0f-abf7-47c3-8466-802d3f221a4b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_firstFamilyOperatorEnd_akCount_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_firstFamilyOperatorEnd_alphaL_eq


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < alphaL h L 𝔭 := by
  rw [firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := 2 * vd h L 𝔭 + 1) le_rfl]
  have hN : 0 < Ideal.absNorm 𝔭 := by
    haveI := h𝔭
    exact Nat.pos_of_ne_zero fun h0 =>
      Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭 (Ideal.absNorm_eq_zero_iff.mp h0)
  apply div_pos
  · exact_mod_cast firstFamilyOperatorEnd.akCount_pos hF hs hd hL hLi h𝔭 _
  · apply pow_pos
    exact_mod_cast hN
end Formalism.HermitianLattices.Ext.L3
