-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.isLatticeIn_span_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:48.677561+00:00
-- url     : https://prove2.me/submissions/891e7ce8-b9fe-4296-aa9e-451cf9819d3b

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
variable {V V' : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V']
  [IsScalarTower O (FractionRing O) V']
namespace Formalism.RepresentationBoundsCohomology.LOC.Lat2
theorem _root_.solution {n : ℕ} (e : Basis (Fin n) (FractionRing O) V) :
    IsLatticeIn (Submodule.span O (Set.range e)) := by
  refine ⟨Submodule.fg_span (Set.finite_range e), ?_⟩
  rw [Submodule.span_span_of_tower, e.span_eq]
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
