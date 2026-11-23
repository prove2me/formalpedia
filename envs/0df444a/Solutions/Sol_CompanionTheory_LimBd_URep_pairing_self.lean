-- Prove2me | solution 1 for CompanionTheory.LimBd.URep.pairing_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:40.010401+00:00
-- url     : https://prove2.me/submissions/fb20bb29-5fe8-46a5-97d2-cbcd35fd8483

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
theorem _root_.solution (π : UnitaryRep G H) (v w : H) :
    pairing μ π π v w v w = ((∫ g, ‖⟪w, π g v⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  unfold pairing
  rw [← integral_complex_ofReal]
  congr 1
  funext g
  rw [Complex.star_def, Complex.mul_conj']
  push_cast
  rfl
end CompanionTheory.LimBd.URep
