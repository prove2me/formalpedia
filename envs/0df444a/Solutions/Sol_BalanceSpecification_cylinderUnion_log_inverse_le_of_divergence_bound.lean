-- Prove2me | solution 1 for BalanceSpecification.cylinderUnion_log_inverse_le_of_divergence_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:19.806879+00:00
-- url     : https://prove2.me/submissions/b061f31e-1141-4171-8715-3af6113a9c47

module
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_event_log_inverse_le_divergence_add_log_two
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_IsInvariant_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_disjoint_cylinder
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Set Filter
open scoped Topology symmDiff
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution
    {hX : X.carrier.Nonempty} {μ ν : ProbabilityMeasure X.carrier}
    (hG : IsGibbsMeasure hX μ) (hν : IsInvariant ν) {C : ℝ}
    (hD : ∀ n : ℕ, FiniteEntropy.divergence
      (blockDistribution ν (2 * n + 1)) (blockDistribution μ (2 * n + 1)) ≤ C)
    (n : ℕ) (S : Finset (Word A))
    (hS : ∀ w ∈ S, w ∈ language X ∧ w.length = 2 * n + 1)
    (hpos : 0 < (μ : Measure X.carrier).real (⋃ w ∈ S, cylinder X w (-(n : ℤ)))) :
    (ν : Measure X.carrier).real (⋃ w ∈ S, cylinder X w (-(n : ℤ))) *
        Real.log (1 / (μ : Measure X.carrier).real
          (⋃ w ∈ S, cylinder X w (-(n : ℤ)))) ≤ C + Real.log 2 := by
  classical
  let W := wordFinset (language X) (2 * n + 1)
  let T : Finset W := S.subtype (· ∈ W)
  have hSW w (hw : w ∈ S) : w ∈ W := mem_wordFinset.mpr (hS w hw)
  have hd : Set.PairwiseDisjoint (S : Set (Word A))
      (fun w => cylinder X w (-(n : ℤ))) := by
    intro v hv w hw hvw
    exact disjoint_cylinder X ((hS v hv).2.trans (hS w hw).2.symm) hvw _
  have hsum (ρ : ProbabilityMeasure X.carrier) (hρ : IsInvariant ρ) :
      (∑ w ∈ T, blockDistribution ρ (2 * n + 1) w) =
        (ρ : Measure X.carrier).real (⋃ w ∈ S, cylinder X w (-(n : ℤ))) := by
    change (∑ w ∈ S.subtype (· ∈ W),
      (ρ : Measure X.carrier).real (cylinder X w.val 0)) = _
    rw [Finset.sum_subtype_of_mem
      (fun w : Word A => (ρ : Measure X.carrier).real (cylinder X w 0)) hSW]
    rw [measureReal_biUnion_finset hd (fun w _ => measurableSet_cylinder X w _)]
    apply Finset.sum_congr rfl
    intro w _
    exact (hρ.cylinder_real_eq_zero w _).symm
  have hq w : 0 < blockDistribution μ (2 * n + 1) w :=
    hG.cylinder_real_pos (mem_wordFinset.mp w.property).1 0
  have hTpos : 0 < ∑ w ∈ T, blockDistribution μ (2 * n + 1) w := by
    rw [hsum μ hG.1]
    exact hpos
  have H := FiniteEntropy.event_log_inverse_le_divergence_add_log_two
    (p := blockDistribution ν (2 * n + 1)) (q := blockDistribution μ (2 * n + 1))
    (fun _ => measureReal_nonneg) hq (blockDistribution_sum ν _) (blockDistribution_sum μ _) T hTpos
  rw [hsum ν hν, hsum μ hG.1] at H
  linarith only [H, hD n]
end BalanceSpecification
