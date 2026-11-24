-- Prove2me | solution 1 for BalanceSpecification.continuous_cylinder_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:20.411379+00:00
-- url     : https://prove2.me/submissions/f059bda2-5c39-4cac-9d49-b77a3c4e285b

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Theorems.Thm_BalanceSpecification_continuous_probabilityReal_of_isClopen
public import Theorems.Thm_BalanceSpecification_isClosed_cylinder
public import Theorems.Thm_BalanceSpecification_isOpen_cylinder


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
theorem _root_.solution (X : ShiftSpace A) (w : Word A) (k : ℤ) :
    Continuous (fun μ : ProbabilityMeasure X.carrier =>
      (μ : Measure X.carrier).real (cylinder X w k)) :=
  continuous_probabilityReal_of_isClopen ⟨isClosed_cylinder X w k, isOpen_cylinder X w k⟩
end BalanceSpecification
