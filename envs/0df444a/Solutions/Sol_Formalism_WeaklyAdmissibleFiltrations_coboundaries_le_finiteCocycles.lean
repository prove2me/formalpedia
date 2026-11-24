-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.coboundaries_le_finiteCocycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:08:24.073749+00:00
-- url     : https://prove2.me/submissions/ff10f3c7-8227-4c98-a425-1d526fa3226b

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_Galois
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_coboundaryMap_mem_finiteCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}
variable [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul LL V]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (hcont : ∀ x, Continuous fun g => ρ g x) : B1 ρ ≤ finiteCocycles PD ρ := by
  rintro c ⟨x, rfl⟩
  exact coboundaryMap_mem_finiteCocycles hcont x
end Formalism.WeaklyAdmissibleFiltrations
