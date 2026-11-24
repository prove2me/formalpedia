-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.alphaN_rank_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:15:54.37698+00:00
-- url     : https://prove2.me/submissions/9f3cddc4-117a-4c86-9c98-acfa4f358261

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_congrP_algebraMap_iff_sub_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_alphaN_eq_of_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mem_pow_iff_le_vF
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hm : finrank K V = 0) {n : 𝓞 F} (hn : n ≠ 0) : alphaN h L 𝔭 n = 0 := by
  have hsub : Subsingleton V := finrank_zero_iff.1 hm
  rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn le_rfl]
  have h0 : nkCount h L 𝔭 (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) n = 0 := by
    unfold nkCount
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨x, y, -, hc⟩
    have hy : h (y : V) (y : V) = algebraMap F K ((0 : 𝓞 F) : F) := by
      rw [Subsingleton.elim (y : V) 0]
      simp
    rw [hy, MeanB.congrP_algebraMap_iff_sub_mem h𝔭, zero_sub, neg_mem_iff, mem_pow_iff_le_vF h𝔭 hn] at hc
    omega
  rw [h0]
  simp
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
