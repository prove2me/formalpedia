-- Prove2me | solution 1 for BalanceSpecification.upperSemicontinuous_measureEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:38.89981+00:00
-- url     : https://prove2.me/submissions/27e1e114-77fc-4a4c-84a0-f9bd438195bd

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Theorems.Thm_BalanceSpecification_continuous_blockEntropy
public import Theorems.Thm_BalanceSpecification_measureEntropy_eq_iInf
public import Theorems.Thm_BalanceSpecification_blockEntropy_nonneg


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
theorem _root_.solution :
    UpperSemicontinuous (fun μ : {μ : ProbabilityMeasure X.carrier // IsInvariant μ} =>
      measureEntropy μ.val μ.property) := by
  let : Nonempty {n : ℕ // 1 ≤ n} := ⟨⟨1, le_rfl⟩⟩
  have heq : (fun μ : {μ : ProbabilityMeasure X.carrier // IsInvariant μ} =>
      measureEntropy μ.val μ.property) =
      fun μ => ⨅ n : {n : ℕ // 1 ≤ n}, blockEntropy μ.val n.val / n.val := by
    funext μ
    exact measureEntropy_eq_iInf μ.property
  rw [heq]
  apply upperSemicontinuous_ciInf
  · intro μ
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (blockEntropy_nonneg μ.val n.val) (Nat.cast_nonneg n.val)
  · intro n
    exact (((continuous_blockEntropy X n.val).comp continuous_subtype_val).div_const
      (n.val : ℝ)).upperSemicontinuous
end BalanceSpecification
