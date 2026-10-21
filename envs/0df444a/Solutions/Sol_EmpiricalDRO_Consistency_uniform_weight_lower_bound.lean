-- Prove2me | solution 1 for EmpiricalDRO.Consistency.uniform_weight_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:22:01.734822+00:00
-- url     : https://prove2.me/submissions/4aa791d3-6276-436c-9f41-aa9c52814d3b

import Mathlib
import Definitions.Def_EmpiricalDRO_Consistency_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ ρ : ℝ) (hρ : 0 ≤ ρ) :
    (1 / (n : ℝ)) * ∑ i, (z i - μ) ≤ GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg ρ z - μ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : (fun _ : Fin n => (1 : ℝ) / n) ∈
      PhiDivRobust.Counterpart.probUncertaintySet EmpiricalDRO.Coverage.burg (fun _ => (1 : ℝ) / n) (ρ / n) := by
    refine ⟨fun i => by positivity, ?_, ?_⟩
    · simp [Finset.sum_const, Finset.card_univ]
      field_simp
    · have h0 : ∀ i : Fin n, (((1 : ℝ) / n : ℝ) : EReal) *
          EmpiricalDRO.Coverage.burg (((1 : ℝ) / n) / ((1 : ℝ) / n)) = 0 := by
        intro i
        rw [div_self (by positivity)]
        simp [EmpiricalDRO.Coverage.burg]
      show ∑ i : Fin n, (((1 : ℝ) / n : ℝ) : EReal) *
          EmpiricalDRO.Coverage.burg (((1 : ℝ) / n) / ((1 : ℝ) / n)) ≤ _
      rw [Finset.sum_eq_zero (fun i _ => h0 i)]
      exact_mod_cast (by positivity : (0 : ℝ) ≤ ρ / n)
  have hbdd : BddAbove ((fun p : Fin n → ℝ => ∑ i, p i * z i) ''
      PhiDivRobust.Counterpart.probUncertaintySet EmpiricalDRO.Coverage.burg (fun _ => (1 : ℝ) / n) (ρ / n)) := by
    refine ⟨∑ i, |z i|, ?_⟩
    rintro _ ⟨p, ⟨hp0, hp1, _⟩, rfl⟩
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hpi : p i ≤ 1 := by
      rw [← hp1]
      exact Finset.single_le_sum (f := p) (fun j _ => hp0 j) (Finset.mem_univ i)
    calc p i * z i ≤ p i * |z i| := mul_le_mul_of_nonneg_left (le_abs_self _) (hp0 i)
      _ ≤ 1 * |z i| := mul_le_mul_of_nonneg_right hpi (abs_nonneg _)
      _ = |z i| := one_mul _
  have hle : ∑ i, (fun _ : Fin n => (1 : ℝ) / n) i * z i ≤ sSup ((fun p : Fin n → ℝ => ∑ i, p i * z i) ''
      PhiDivRobust.Counterpart.probUncertaintySet EmpiricalDRO.Coverage.burg (fun _ => (1 : ℝ) / n) (ρ / n)) :=
    le_csSup hbdd ⟨_, hmem, rfl⟩
  have heq : ∑ i, (fun _ : Fin n => (1 : ℝ) / n) i * z i = (1 / (n : ℝ)) * ∑ i, z i := by
    rw [Finset.mul_sum]
  unfold GenEmpLik.Expansion.robustMean
  have hs : (1 / (n : ℝ)) * ∑ i, (z i - μ) = (1 / (n : ℝ)) * ∑ i, z i - μ := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, Finset.card_univ]
    field_simp
  rw [hs]
  linarith [heq, hle]
