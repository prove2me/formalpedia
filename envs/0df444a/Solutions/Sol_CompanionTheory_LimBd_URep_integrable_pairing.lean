-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.integrable_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:22.900306+00:00
-- url     : https://prove2.me/submissions/52e565c7-3f04-45c7-a880-368d28c46a88

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.URep
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace CompanionTheory.LimBd.URep
theorem _root_.solution {π : UnitaryRep G H} {σ : UnitaryRep G K} (hπ : SqInt μ π) (hσ : SqInt μ σ)
    (v w : H) (v' w' : K) : Integrable (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ :=
  (hπ v w).integrable_mul (hσ v' w').star
end CompanionTheory.LimBd.URep
