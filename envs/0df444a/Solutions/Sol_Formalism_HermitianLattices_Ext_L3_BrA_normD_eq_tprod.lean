-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BrA.normD_eq_tprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:39.783009+00:00
-- url     : https://prove2.me/submissions/35547942-023e-442a-b616-8792cdb7e159

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanEqProd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_absNorm_eq_tprod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_discrIdeal_eq_map
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_normD_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_vd_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_aniso_of_totPosDef
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_discrIdeal_ne_bot


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
namespace BrA
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    normD h L = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hD' : BrA.discrF F h L ≠ ⊥ := by
    intro e
    apply hD
    rw [BrA.discrIdeal_eq_map hF hs, e, Ideal.map_bot]
  rw [BrA.normD_eq hK hF hs, BrA.absNorm_eq_tprod hD']
  exact tprod_congr fun 𝔭 => by rw [BrA.vd_eq hF hs]
end BrA
end Formalism.HermitianLattices.Ext.L3
