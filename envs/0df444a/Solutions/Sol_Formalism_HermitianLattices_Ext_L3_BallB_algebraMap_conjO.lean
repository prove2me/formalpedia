-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.algebraMap_conjO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:11.544819+00:00
-- url     : https://prove2.me/submissions/f7314752-d64d-42cb-b3a0-4d465ead400f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution (x : 𝓞 K) :
    algebraMap (𝓞 K) K (conjO K x) = star (algebraMap (𝓞 K) K x) := rfl
end Formalism.HermitianLattices.Ext.L3.BallB
