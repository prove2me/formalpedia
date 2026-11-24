-- Prove2me | solution 1 for BalanceSpecification.exists_entropy_maximizing_invariant_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:32.245843+00:00
-- url     : https://prove2.me/submissions/8785f18e-65ad-4789-9439-049875db96ce

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Theorems.Thm_BalanceSpecification_upperSemicontinuous_measureEntropy
public import Theorems.Thm_BalanceSpecification_isClosed_setOf_isInvariant
public import Theorems.Thm_BalanceSpecification_exists_invariant_probability

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
    ∃ (μ : ProbabilityMeasure X.carrier) (hInv : IsInvariant μ),
      ∀ (ν : ProbabilityMeasure X.carrier) (hν : IsInvariant ν),
        measureEntropy ν hν ≤ measureEntropy μ hInv := by
  let : CompactSpace X.carrier := isCompact_iff_compactSpace.mp X.isClosed.isCompact
  let : CompactSpace {μ : ProbabilityMeasure X.carrier // IsInvariant μ} :=
    isCompact_iff_compactSpace.mp (isClosed_setOf_isInvariant X).isCompact
  obtain ⟨μ, hμ⟩ := exists_invariant_probability hX
  have hne : (univ : Set {μ : ProbabilityMeasure X.carrier // IsInvariant μ}).Nonempty :=
    ⟨⟨μ, hμ⟩, mem_univ _⟩
  obtain ⟨ν, _, hν⟩ := (upperSemicontinuous_measureEntropy.upperSemicontinuousOn univ).exists_isMaxOn
    hne isCompact_univ
  refine ⟨ν.val, ν.property, ?_⟩
  intro η hη
  exact hν (mem_univ (⟨η, hη⟩ : {μ : ProbabilityMeasure X.carrier // IsInvariant μ}))
end BalanceSpecification
