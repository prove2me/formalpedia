-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.Lat2.dualLat_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:45.613294+00:00
-- url     : https://prove2.me/submissions/5a181d9b-ff58-4d80-a1cd-09a730bbf568

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
  [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V']
namespace Formalism.RepresentationBoundsCohomology.LOC.Lat2
theorem _root_.solution {G : Type u} [Group G] {ε : G →* Oˣ} {ρ : Representation O G V}
    {ρ' : Representation O G V'} {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {T : Submodule O V}
    (hs : StableUnder ρ T) (he : EquivPair ε ρ ρ' b) : StableUnder ρ' (dualLat b T) := by
  intro g f hf x hx
  have hx' : x = ρ g (ρ g⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hx', he]
  exact Submodule.smul_mem _ _ (hf _ (hs g⁻¹ x hx))
end Formalism.RepresentationBoundsCohomology.LOC.Lat2
