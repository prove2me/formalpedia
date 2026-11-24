-- Prove2me | solution 1 for BalanceSpecification.entropy_eq_sup_measureEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:23:12.441898+00:00
-- url     : https://prove2.me/submissions/0f353fb5-45bf-4aa0-b9a5-3c7257edce4c

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_exists_maximalEntropyMeasure
public import Theorems.Thm_BalanceSpecification_measureEntropy_le_entropy


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
    entropy X hX = sSup {r : ℝ | ∃ (μ : ProbabilityMeasure X.carrier) (hInv : IsInvariant μ),
      measureEntropy μ hInv = r} := by
  obtain ⟨μ, hμ, hmax⟩ := exists_maximalEntropyMeasure hX
  have hbound : BddAbove {r : ℝ | ∃ (ν : ProbabilityMeasure X.carrier) (hInv : IsInvariant ν),
      measureEntropy ν hInv = r} := by
    refine ⟨entropy X hX, ?_⟩
    rintro r ⟨ν, hν, rfl⟩
    exact measureEntropy_le_entropy hX hν
  apply le_antisymm
  · exact le_csSup hbound ⟨μ, hμ, hmax⟩
  · have hne : {r : ℝ | ∃ (ν : ProbabilityMeasure X.carrier) (hInv : IsInvariant ν),
        measureEntropy ν hInv = r}.Nonempty := ⟨measureEntropy μ hμ, μ, hμ, rfl⟩
    exact csSup_le hne (by
      rintro r ⟨ν, hν, rfl⟩
      exact measureEntropy_le_entropy hX hν)
end BalanceSpecification
