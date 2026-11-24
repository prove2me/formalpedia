-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.integral_of_mem_genus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:50.376454+00:00
-- url     : https://prove2.me/submissions/4bffea63-d06d-42d3-8434-1bad9a456212

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinMemGenusIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isIntegralLat_of_ortho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isLattice_of_ortho


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
open Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n) (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h L := by
  obtain ⟨-, -, hi⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  exact ((hi I L (isLattice_of_ortho hI).fg hL.1.fg hL.2).2).mp (isIntegralLat_of_ortho hI)
end Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
