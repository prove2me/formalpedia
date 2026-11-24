-- Prove2me | solution 1 for BalanceSpecification.exists_invariant_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:24.472301+00:00
-- url     : https://prove2.me/submissions/e8ae5b4a-e234-4682-a4a5-3507e86e138d

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Theorems.Thm_BalanceSpecification_continuous_shiftMap
public import Theorems.Thm_BalanceSpecification_exists_measurePreserving_mapClusterPt_finiteOrbitProbability


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty) :
    ∃ μ : ProbabilityMeasure X.carrier, IsInvariant μ := by
  classical
  let x : X.carrier := ⟨hX.choose, hX.choose_spec⟩
  let : CompactSpace X.carrier := isCompact_iff_compactSpace.mp X.isClosed.isCompact
  obtain ⟨μ, hμ, hinv⟩ := exists_measurePreserving_mapClusterPt_finiteOrbitProbability
    (I := fun _ => Unit) (continuous_shiftMap X) (fun _ _ => x)
  exact ⟨μ, hinv⟩
end BalanceSpecification
