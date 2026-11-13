-- Prove2me | solution 1 for CountingLLL.RandomRAM.reciprocal_expected_cost
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:40:01.681227+00:00
-- url     : https://prove2.me/submissions/99fe3c84-1803-4578-9247-1f839851e8f6

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace ResearchReciprocalCost

variable {β : Type} [MeasurableSpace β]

def survive (S : Set β) (n : ℕ) : Set (ℕ → β) := {ω | ∀ i < n, ω i ∈ S}

private theorem survive_measurable (S : Set β) (hS : MeasurableSet S) (n : ℕ) :
    MeasurableSet (survive S n) := by
  have heq : survive S n = ⋂ i : Fin n, {ω : ℕ → β | ω i.val ∈ S} := by
    ext ω
    simp only [survive, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i
      exact h i.val i.isLt
    · intro h i hi
      exact h ⟨i, hi⟩
  rw [heq]
  exact MeasurableSet.iInter fun i => hS.preimage (measurable_pi_apply i.val)

/-- Samples may carry their own correlated costs: independence is only across samples. -/
noncomputable def totalCost (S : Set β) (K : β → ℝ≥0∞) (ω : ℕ → β) : ℝ≥0∞ :=
  ∑' n : ℕ, (survive S n).indicator (fun ω => K (ω n)) ω

private theorem single_cost (ν : Measure β) [IsProbabilityMeasure ν]
    (S : Set β) (hS : MeasurableSet S) (K : β → ℝ≥0∞) (hK : Measurable K) (n : ℕ) :
    (∫⁻ ω, (survive S n).indicator (fun ω => K (ω n)) ω
      ∂(Measure.infinitePi fun _ : ℕ => ν)) = ν S ^ n * ∫⁻ x, K x ∂ν := by
  classical
  let φ : ℕ → β → ℝ≥0∞ := fun i x => if i = n then K x else S.indicator 1 x
  have hφ : ∀ i, Measurable (φ i) := by
    intro i
    by_cases h : i = n
    · simpa [φ, h] using hK
    · simpa [φ, h] using (measurable_one.indicator hS : Measurable (S.indicator (1 : β → ℝ≥0∞)))
  have hind : iIndepFun (fun i (ω : ℕ → β) => φ i (ω i))
      (Measure.infinitePi fun _ : ℕ => ν) := iIndepFun_infinitePi hφ
  have hmeas : ∀ i, Measurable (fun ω : ℕ → β => φ i (ω i)) :=
    fun i => (hφ i).comp (measurable_pi_apply i)
  have heval : ∀ i, (∫⁻ ω, φ i (ω i) ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      ∫⁻ x, φ i x ∂ν := by
    intro i
    rw [← lintegral_map (hφ i) (measurable_pi_apply i), Measure.infinitePi_map_eval]
  have hprodpoint : ∀ ω : ℕ → β,
      (∏ i ∈ Finset.range (n + 1), φ i (ω i)) =
        (survive S n).indicator (fun ω => K (ω n)) ω := by
    intro ω
    by_cases hw : ω ∈ survive S n
    · have hpre : (∏ i ∈ Finset.range n, φ i (ω i)) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        simp [φ, ne_of_lt hi', Set.indicator_of_mem (hw i hi')]
      rw [Finset.prod_range_succ, hpre]
      simp [φ, hw]
    · have hex : ∃ i < n, ω i ∉ S := by
        simpa [survive, not_forall] using hw
      obtain ⟨i, hi, hni⟩ := hex
      have hpre : (∏ i ∈ Finset.range n, φ i (ω i)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
        simp [φ, ne_of_lt hi, hni]
      rw [Finset.prod_range_succ, hpre]
      simp [hw]
  have hcalc := lintegral_prod_eq_prod_lintegral_of_indepFun
    (Finset.range (n + 1)) (fun i (ω : ℕ → β) => φ i (ω i)) hind hmeas
  simp_rw [heval] at hcalc
  simp_rw [hprodpoint] at hcalc
  rw [hcalc, Finset.prod_range_succ]
  have hpre : (∏ i ∈ Finset.range n, ∫⁻ x, φ i x ∂ν) = ν S ^ n := by
    calc
      _ = ∏ _i ∈ Finset.range n, ν S := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [φ, ne_of_lt (Finset.mem_range.mp hi), lintegral_indicator_one hS]
      _ = _ := by simp
  rw [hpre]
  simp [φ]

/-- Expected total cost with arbitrary dependence between each sample and its own cost. -/
theorem expected_total_cost (ν : Measure β) [IsProbabilityMeasure ν]
    (S : Set β) (hS : MeasurableSet S) (K : β → ℝ≥0∞) (hK : Measurable K) :
    (∫⁻ ω, totalCost S K ω ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫⁻ x, K x ∂ν) / (1 - ν S) := by
  unfold totalCost
  have hm : ∀ n, AEMeasurable ((survive S n).indicator (fun ω => K (ω n)))
      (Measure.infinitePi fun _ : ℕ => ν) := fun n =>
    ((hK.comp (measurable_pi_apply n)).indicator (survive_measurable S hS n)).aemeasurable
  rw [lintegral_tsum hm]
  simp_rw [single_cost ν S hS K hK]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  simp [div_eq_mul_inv, mul_comm]

end ResearchReciprocalCost

open ResearchReciprocalCost

theorem solution {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (S : Set β) (hS : MeasurableSet S) (K : β → ℝ≥0∞) (hK : Measurable K) :
    (∫⁻ ω, ∑' n : ℕ,
      ({ω' : ℕ → β | ∀ i < n, ω' i ∈ S}).indicator (fun ω => K (ω n)) ω
      ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫⁻ x, K x ∂ν) / (1 - ν S) :=
  expected_total_cost ν S hS K hK
