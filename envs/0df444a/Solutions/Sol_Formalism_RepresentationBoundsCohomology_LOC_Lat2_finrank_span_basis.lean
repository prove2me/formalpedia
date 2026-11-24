-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.finrank_span_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:47.709335+00:00
-- url     : https://prove2.me/submissions/9a8f4a47-6e66-4685-8897-11d5a775c4ae

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
    finrank O (Submodule.span O (Set.range e)) = n := by
  have h : LinearIndependent O e :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).2 e.linearIndependent
  rw [finrank_span_eq_card h, Fintype.card_fin]
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
