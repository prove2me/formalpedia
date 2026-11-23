-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.isLattice_mapE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:16:44.866695+00:00
-- url     : https://prove2.me/submissions/fccb39bf-3f35-4bc4-8bd6-cfcebf1f5306

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (mapE φ M) := by
  constructor
  · exact hM.fg.map _
  · have e : ((mapE φ M : Submodule (𝓞 K) V') : Set V') = (φ : V →ₗ[K] V') '' (M : Set V) := rfl
    rw [e, Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearEquiv.range]
end Formalism.HermitianLattices.Ext.L3.RankOne
