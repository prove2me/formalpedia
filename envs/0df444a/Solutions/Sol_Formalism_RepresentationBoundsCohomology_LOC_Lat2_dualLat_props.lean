-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.dualLat_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:04.572898+00:00
-- url     : https://prove2.me/submissions/64800876-e47f-47c0-8ec9-13153adb1f2b

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_exists_basis_of_lattice
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_isLatticeIn_span_basis
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_finrank_span_basis
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_exists_dual_basis
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_dualLat_span

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
theorem _root_.solution {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {T : Submodule O V}
    (hT : IsLatticeIn T) (hb : PerfectRight b) :
    IsLatticeIn (dualLat b T) ∧ finrank O (dualLat b T) = finrank O T ∧
      dualLat b.flip (dualLat b T) = T := by
  obtain ⟨n, e, hTe, hn⟩ := exists_basis_of_lattice hT
  obtain ⟨f, h1, h2⟩ := exists_dual_basis hb e
  have hd : dualLat b T = Submodule.span O (Set.range f) := by
    rw [hTe]; exact dualLat_span e f h2
  refine ⟨?_, ?_, ?_⟩
  · rw [hd]; exact isLatticeIn_span_basis f
  · rw [hd, hn]; exact finrank_span_basis f
  · rw [hd, hTe]; exact dualLat_span (b := b.flip) f e h1
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
