-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinD.alphaL_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:09.626565+00:00
-- url     : https://prove2.me/submissions/c9240f2b-2175-4b98-bb50-cfb960d38759

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealSmulLeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocFSpanConsBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsTotPosDefOfSmul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_firstFamilyOperatorEnd_alphaL_eq


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinD
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.PinD
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 2 ≤ k) :
    alphaL h L 𝔭 = (akCount h L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  exact firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (by omega)
end Formalism.HermitianLattices.Ext.L3.PinD
