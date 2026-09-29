-- Prove2me | solution 1 for DSSYKScales.string_hamiltonian_fluctuation_finite
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:37:26.777188+00:00
-- url     : https://prove2.me/submissions/7aab4e95-fecb-4c64-b007-cb1a35c4bbea

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales

/-- Algebraic form of the string second moment. -/
theorem aux_shf_identity (N q : ℕ) (J : ℝ) (hq1 : 1 ≤ q) (hqN : q ≤ N) :
    stringHamiltonianSecondMoment N q J =
      J ^ 2 * (((q : ℝ) ^ 2 / (N : ℝ))⁻¹ *
        ∏ i ∈ Finset.range q, (1 - (i : ℝ) / (N : ℝ))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : (N.choose q : ℝ) * (q.factorial : ℝ) = ∏ i ∈ Finset.range q, ((N : ℝ) - i) := by
    rw [← Nat.cast_mul, mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have := Finset.mem_range.1 hi
    rw [Nat.cast_sub (by omega)]
  have h2 : ∏ i ∈ Finset.range q, ((N : ℝ) - i) =
      (N : ℝ) ^ q * ∏ i ∈ Finset.range q, (1 - (i : ℝ) / N) := by
    have : (N : ℝ) ^ q = (N : ℝ) ^ (Finset.range q).card := by rw [Finset.card_range]
    rw [this, Finset.pow_card_mul_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    field_simp
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  unfold stringHamiltonianSecondMoment cosmicHamiltonianSecondMoment
  have h3 : (N.choose (k + 1) : ℝ) * (((k + 1).factorial : ℝ) / (N : ℝ) ^ (k + 1 - 1) * J ^ 2)
      = ((N.choose (k + 1) : ℝ) * ((k + 1).factorial : ℝ)) / (N : ℝ) ^ k * J ^ 2 := by
    rw [Nat.add_sub_cancel]; ring
  rw [h3, h1, h2, pow_succ]
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Lower bound `exp(-x - 2x^2) ≤ 1 - x` for `0 ≤ x ≤ 1/2`. -/
theorem aux_shf_exp_lower (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    Real.exp (-x - 2 * x ^ 2) ≤ 1 - x := by
  have hx : 0 < 1 - x := by linarith
  have hy : Real.exp (-(x / (1 - x))) ≤ 1 - x := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hx]
    have : (1 - x)⁻¹ = x / (1 - x) + 1 := by field_simp; ring
    rw [this]
    exact Real.add_one_le_exp _
  refine le_trans (Real.exp_le_exp.mpr ?_) hy
  have : x / (1 - x) ≤ x + 2 * x ^ 2 := by
    rw [div_le_iff₀ hx]; nlinarith [sq_nonneg x]
  linarith

theorem aux_shf_sum_id (q : ℕ) : ∑ i ∈ Finset.range q, (i : ℝ) = (q : ℝ) * ((q : ℝ) - 1) / 2 := by
  induction q with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Two-sided exponential bounds for the product. -/
theorem aux_shf_prod_bounds (a : ℝ) (q : ℕ) (ha : 0 < a) (hq : (q : ℝ) ≤ a / 2) :
    Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / (2 * a)) - 2 * ((q : ℝ) ^ 3 / a ^ 2)) ≤
        ∏ i ∈ Finset.range q, (1 - (i : ℝ) / a) ∧
      ∏ i ∈ Finset.range q, (1 - (i : ℝ) / a) ≤ Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / (2 * a))) := by
  have hS1 : ∑ i ∈ Finset.range q, (i : ℝ) / a = (q : ℝ) * ((q : ℝ) - 1) / (2 * a) := by
    rw [← Finset.sum_div, aux_shf_sum_id]; field_simp
  have hxi : ∀ i ∈ Finset.range q, 0 ≤ (i : ℝ) / a ∧ (i : ℝ) / a ≤ 1 / 2 := by
    intro i hi
    have hiq : (i : ℝ) < q := by exact_mod_cast Finset.mem_range.1 hi
    refine ⟨div_nonneg (Nat.cast_nonneg _) ha.le, ?_⟩
    rw [div_le_iff₀ ha]; linarith
  constructor
  · have hS2 : ∑ i ∈ Finset.range q, ((i : ℝ) / a) ^ 2 ≤ (q : ℝ) ^ 3 / a ^ 2 := by
      calc ∑ i ∈ Finset.range q, ((i : ℝ) / a) ^ 2
          ≤ ∑ _i ∈ Finset.range q, ((q : ℝ) / a) ^ 2 := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hiq : (i : ℝ) < q := by exact_mod_cast Finset.mem_range.1 hi
            refine pow_le_pow_left₀ (hxi i hi).1 ?_ 2
            exact div_le_div_of_nonneg_right hiq.le ha.le
        _ = (q : ℝ) ^ 3 / a ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    calc Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / (2 * a)) - 2 * ((q : ℝ) ^ 3 / a ^ 2))
        ≤ Real.exp (∑ i ∈ Finset.range q, (-((i : ℝ) / a) - 2 * ((i : ℝ) / a) ^ 2)) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hS1]
          linarith
      _ = ∏ i ∈ Finset.range q, Real.exp (-((i : ℝ) / a) - 2 * ((i : ℝ) / a) ^ 2) :=
          Real.exp_sum _ _
      _ ≤ ∏ i ∈ Finset.range q, (1 - (i : ℝ) / a) := by
          refine Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) (fun i hi => ?_)
          exact aux_shf_exp_lower _ (hxi i hi).1 (hxi i hi).2
  · calc ∏ i ∈ Finset.range q, (1 - (i : ℝ) / a)
        ≤ ∏ i ∈ Finset.range q, Real.exp (-((i : ℝ) / a)) := by
          refine Finset.prod_le_prod (fun i hi => ?_) (fun i _ => ?_)
          · linarith [(hxi i hi).2]
          · have := Real.add_one_le_exp (-((i : ℝ) / a)); linarith
      _ = Real.exp (∑ i ∈ Finset.range q, -((i : ℝ) / a)) := (Real.exp_sum _ _).symm
      _ = Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / (2 * a))) := by
          rw [Finset.sum_neg_distrib, hS1]

end DSSYKScales

open DSSYKScales
open Filter Topology

theorem solution (N q : ℕ → ℕ) (lam J : ℝ)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => stringHamiltonianSecondMoment (N n) (q n) J)
      atTop (𝓝 (J ^ 2 * Real.exp (-(lam / 2)) / lam)) := by
  obtain ⟨hlam, hN, hq⟩ := hlim
  have hNinv : Tendsto (fun n => ((N n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN
  have hsq : Tendsto (fun n => ((q n : ℝ) / N n) ^ 2) atTop (𝓝 0) := by
    have := hq.mul hNinv
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hratio : Tendsto (fun n => (q n : ℝ) / N n) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at this
    refine this.congr (fun n => ?_)
    simp only [Function.comp]
    exact Real.sqrt_sq (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hS1 : Tendsto (fun n => (q n : ℝ) * ((q n : ℝ) - 1) / (2 * N n)) atTop (𝓝 (lam / 2)) := by
    have := (hq.sub hratio).div_const 2
    rw [sub_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hS2 : Tendsto (fun n => 2 * ((q n : ℝ) ^ 3 / (N n : ℝ) ^ 2)) atTop (𝓝 0) := by
    have := (hq.mul hratio).const_mul 2
    rw [mul_zero, mul_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hup : Tendsto (fun n => Real.exp (-((q n : ℝ) * ((q n : ℝ) - 1) / (2 * N n))))
      atTop (𝓝 (Real.exp (-(lam / 2)))) :=
    (Real.continuous_exp.tendsto _).comp hS1.neg
  have hlow : Tendsto (fun n => Real.exp (-((q n : ℝ) * ((q n : ℝ) - 1) / (2 * N n)) -
      2 * ((q n : ℝ) ^ 3 / (N n : ℝ) ^ 2))) atTop (𝓝 (Real.exp (-(lam / 2)))) := by
    have := (Real.continuous_exp.tendsto _).comp (hS1.neg.sub hS2)
    rw [sub_zero] at this
    exact this
  have hEpos : ∀ᶠ n in atTop, (0 : ℝ) < N n := hN.eventually_gt_atTop 0
  have hEhalf : ∀ᶠ n in atTop, (q n : ℝ) / N n < 1 / 2 :=
    hratio.eventually (eventually_lt_nhds (by norm_num))
  have hEq1 : ∀ᶠ n in atTop, lam / 2 < (q n : ℝ) ^ 2 / N n :=
    hq.eventually (eventually_gt_nhds (by linarith))
  have hEbound : ∀ᶠ n in atTop, (q n : ℝ) ≤ (N n : ℝ) / 2 := by
    filter_upwards [hEpos, hEhalf] with n h1 h2
    rw [div_lt_iff₀ h1] at h2
    linarith
  have hP : Tendsto (fun n => ∏ i ∈ Finset.range (q n), (1 - (i : ℝ) / N n))
      atTop (𝓝 (Real.exp (-(lam / 2)))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hEpos, hEbound] with n h1 h2
      exact (aux_shf_prod_bounds _ _ h1 h2).1
    · filter_upwards [hEpos, hEbound] with n h1 h2
      exact (aux_shf_prod_bounds _ _ h1 h2).2
  have hinv : Tendsto (fun n => ((q n : ℝ) ^ 2 / N n)⁻¹) atTop (𝓝 lam⁻¹) := hq.inv₀ hlam.ne'
  have hmain := (hinv.mul hP).const_mul (J ^ 2)
  rw [show J ^ 2 * Real.exp (-(lam / 2)) / lam = J ^ 2 * (lam⁻¹ * Real.exp (-(lam / 2))) by ring]
  refine Tendsto.congr' ?_ hmain
  filter_upwards [hEpos, hEbound, hEq1] with n h1 h2 h3
  have hq1 : 1 ≤ q n := by
    rcases Nat.eq_zero_or_pos (q n) with h | h
    · rw [h] at h3; simp at h3; linarith
    · exact h
  have hqN : q n ≤ N n := by
    have : (q n : ℝ) ≤ N n := by linarith
    exact_mod_cast this
  rw [aux_shf_identity _ _ _ hq1 hqN]
