-- Prove2me | solution 1 for ChannelCapacity.entropy_strictlyConcave
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:36.712938+00:00
-- url     : https://prove2.me/submissions/c83969ab-1797-41d7-b7be-16e1b259f11e

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_convexCombination_toReal_apply
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_dirac
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_id
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
namespace ChannelCapacity
theorem _root_.solution (p q : ProbabilityMeasure α) (h_ne : p ≠ q)
    (t : NNReal) (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    ProbabilityMeasure.entropy (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
      (t : ℝ) * ProbabilityMeasure.entropy p + (1 - (t : ℝ)) * ProbabilityMeasure.entropy q := by
  have hneq_coord : ∃ a : α, (p.toMeasure {a}).toReal ≠ (q.toMeasure {a}).toReal := by
    by_contra h_eq
    have h_eq' : ∀ a : α, (p.toMeasure {a}).toReal = (q.toMeasure {a}).toReal := by
      simpa using not_exists.mp h_eq
    apply h_ne
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_singleton
    intro a
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h_eq' a)
  obtain ⟨a0, ha0⟩ := hneq_coord
  have ht_pos' : 0 < (t : ℝ) := by exact_mod_cast ht_pos
  have h1mt_pos : 0 < 1 - (t : ℝ) := by
    linarith [show (t : ℝ) < 1 by exact_mod_cast ht_lt_one]
  have hle :
      ∀ a : α,
        (t : ℝ) * Real.negMulLog ((p.toMeasure {a}).toReal) +
            (1 - (t : ℝ)) * Real.negMulLog ((q.toMeasure {a}).toReal) ≤
          Real.negMulLog (((ProbabilityMeasure.convexCombination p q t
            (le_of_lt ht_lt_one)).toMeasure {a}).toReal) := by
    intro a
    rw [convexCombination_toReal_apply]
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (Real.concaveOn_negMulLog.2
        (ENNReal.toReal_nonneg : (p.toMeasure {a}).toReal ∈ Set.Ici (0 : ℝ))
        (ENNReal.toReal_nonneg : (q.toMeasure {a}).toReal ∈ Set.Ici (0 : ℝ))
        (show 0 ≤ (t : ℝ) by exact_mod_cast (le_of_lt ht_pos))
        (show 0 ≤ 1 - (t : ℝ) by linarith [show (t : ℝ) < 1 by exact_mod_cast ht_lt_one])
        (by ring : (t : ℝ) + (1 - (t : ℝ)) = 1))
  have hlt :
      (t : ℝ) * Real.negMulLog ((p.toMeasure {a0}).toReal) +
          (1 - (t : ℝ)) * Real.negMulLog ((q.toMeasure {a0}).toReal) <
        Real.negMulLog (((ProbabilityMeasure.convexCombination p q t
          (le_of_lt ht_lt_one)).toMeasure {a0}).toReal) := by
    rw [convexCombination_toReal_apply]
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (Real.strictConcaveOn_negMulLog.2
        (ENNReal.toReal_nonneg : (p.toMeasure {a0}).toReal ∈ Set.Ici (0 : ℝ))
        (ENNReal.toReal_nonneg : (q.toMeasure {a0}).toReal ∈ Set.Ici (0 : ℝ))
        ha0 ht_pos' h1mt_pos
        (by ring : (t : ℝ) + (1 - (t : ℝ)) = 1))
  have hweighted :
      (t : ℝ) * ProbabilityMeasure.entropy p + (1 - (t : ℝ)) * ProbabilityMeasure.entropy q =
        ∑ a,
          ((t : ℝ) * Real.negMulLog ((p.toMeasure {a}).toReal) +
            (1 - (t : ℝ)) * Real.negMulLog ((q.toMeasure {a}).toReal)) := by
    rw [ProbabilityMeasure.entropy, ProbabilityMeasure.entropy, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
  rw [ProbabilityMeasure.entropy, hweighted]
  simpa [gt_iff_lt] using Finset.sum_lt_sum (fun a _ha => hle a) ⟨a0, Finset.mem_univ _, hlt⟩
end ChannelCapacity
