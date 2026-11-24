-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.exists_basis_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:46.481937+00:00
-- url     : https://prove2.me/submissions/788807c9-44fd-40bc-ba98-350af876177d

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
theorem _root_.solution {T : Submodule O V} (hT : IsLatticeIn T) :
    ∃ (n : ℕ) (e : Basis (Fin n) (FractionRing O) V),
      T = Submodule.span O (Set.range e) ∧ finrank O T = n := by
  have : Submodule.IsLattice (FractionRing O) T := ⟨hT.1, hT.2⟩
  let B := Module.finBasis O T
  refine ⟨_, B.extendOfIsLattice (FractionRing O), ?_, rfl⟩
  have h : Set.range (B.extendOfIsLattice (FractionRing O)) = T.subtype '' Set.range B := by
    rw [← Set.range_comp]
    congr 1
    ext i
    simp
  rw [h, ← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
