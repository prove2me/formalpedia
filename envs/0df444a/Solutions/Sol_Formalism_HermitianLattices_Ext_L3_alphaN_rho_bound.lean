-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.alphaN_rho_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:14:01.971281+00:00
-- url     : https://prove2.me/submissions/04b60fd5-9f2a-454d-a7fd-c8a55e0cb416

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldFurther
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_geom_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_abs_x_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_alphaN_closed
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_beta_pos


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
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hv : vd h L 𝔭 = 0) {n : 𝓞 F} (hn : n ≠ 0) :
    0 ≤ alphaN h L 𝔭 n / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) ∧ alphaN h L 𝔭 n / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) ≤ 4 := by
  rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd hL hLi h𝔭 hv (by omega) _ n hn rfl,
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne']
  exact unitaryAbsoluteValueBounds.geom_bound (unitaryAbsoluteValueBounds.abs_x_le h𝔭 hm) _
end Formalism.HermitianLattices.Ext.L3
