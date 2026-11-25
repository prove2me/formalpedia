-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StabilizerLattices.smul_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:59.244624+00:00
-- url     : https://prove2.me/submissions/c3dff156-470e-45d0-bdcd-0739f4c7cdeb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Lemmata_GeneralBFactSecondForm_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem

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
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.StabilizerLattices
theorem _root_.solution (g : Formalism.HermitianLatticesTheory.isom h) (Λ : Submodule (𝓞 K) V) : g • Λ = Formalism.HermitianLatticesTheory.gmap g.1 Λ := rfl
end Formalism.HermitianLattices.Ext.L3.StabilizerLattices
