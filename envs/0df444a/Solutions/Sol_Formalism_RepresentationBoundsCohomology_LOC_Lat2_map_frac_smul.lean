-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.map_frac_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:21.302932+00:00
-- url     : https://prove2.me/submissions/96d8613a-0801-46a8-9991-07286e03dd27

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
open Formalism.RepresentationBoundsCohomology.LOC.Lat2
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.RepresentationBoundsCohomology.LOC.Lat2
theorem _root_.solution {V W : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup W] [Module O W] [Module (FractionRing O) W]
    [IsScalarTower O (FractionRing O) W] (f : V →ₗ[O] W) (c : FractionRing O) (x : V) :
    f (c • x) = c • f x :=
  (f.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)).map_smul c x
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
