-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.dualLat_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:44.695832+00:00
-- url     : https://prove2.me/submissions/9a51b223-499a-49cc-a562-013d24d0c3f0

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
omit [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
namespace Formalism.RepresentationBoundsCohomology.LOC.Lat2
theorem _root_.solution {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {n : ℕ} (e : Fin n → V)
    (f : Basis (Fin n) (FractionRing O) V') (h : ∀ i w, f.repr w i = b (e i) w) :
    dualLat b (Submodule.span O (Set.range e)) = Submodule.span O (Set.range f) := by
  ext w
  rw [Basis.mem_span_iff_repr_mem]
  constructor
  · intro hw i
    rw [h]
    exact Submodule.mem_one.1 (hw (e i) (Submodule.subset_span (Set.mem_range_self i)))
  · intro hw
    have hle : Submodule.span O (Set.range e) ≤
        (1 : Submodule O (FractionRing O)).comap (b.flip w) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have := hw i
      rw [h] at this
      exact Submodule.mem_one.2 this
    exact fun x hx => hle hx
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
