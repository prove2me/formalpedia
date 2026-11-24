-- Prove2me | solution 1 for BalanceSpecification.measureEntropy_eq_iInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:46.205921+00:00
-- url     : https://prove2.me/submissions/73ce851f-2a63-4440-9b4a-65b893d4bb3b

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Theorems.Thm_BalanceSpecification_measureEntropy_eq_sInf


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
theorem _root_.solution {μ : ProbabilityMeasure X.carrier} (hInv : IsInvariant μ) :
    measureEntropy μ hInv = ⨅ n : {n : ℕ // 1 ≤ n}, blockEntropy μ n.val / n.val := by
  rw [measureEntropy_eq_sInf]
  change sInf ((fun n : ℕ => blockEntropy μ n / n) '' Ici 1) =
    sInf (range (fun n : {n : ℕ // 1 ≤ n} => blockEntropy μ n.val / n.val))
  congr 1
  ext r
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n.val, n.property, rfl⟩
end BalanceSpecification
