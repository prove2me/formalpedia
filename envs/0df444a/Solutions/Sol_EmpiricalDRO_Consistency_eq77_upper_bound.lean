-- Prove2me | solution 1 for EmpiricalDRO.Consistency.eq77_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:28:23.485073+00:00
-- url     : https://prove2.me/submissions/62623a30-2530-4a02-b5da-b0362840afd1

import Mathlib
import Definitions.Def_EmpiricalDRO_Consistency_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology

lemma edc_burg_nonneg (t : ℝ) : 0 ≤ EmpiricalDRO.Coverage.burg t := by
  unfold EmpiricalDRO.Coverage.burg
  split_ifs with h
  · have := Real.log_le_sub_one_of_pos h
    exact_mod_cast (by linarith : (0 : ℝ) ≤ -Real.log t + t - 1)
  · exact le_top

lemma edc_coe_sum {n : ℕ} (f : Fin n → ℝ) :
    ∑ i, ((f i : ℝ) : EReal) = ((∑ i, f i : ℝ) : EReal) := by
  have : ∀ s : Finset (Fin n), ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]
  exact this _

/-- Membership in the Burg ball: positivity of weights and the real divergence bound. -/
lemma edc_ball {n : ℕ} (hn : 0 < n) (ρ : ℝ) (w : Fin n → ℝ)
    (hw : w ∈ PhiDivRobust.Counterpart.probUncertaintySet EmpiricalDRO.Coverage.burg
      (fun _ => (1 : ℝ) / n) (ρ / n)) :
    (∀ i, 0 < w i) ∧ ∑ i, (1 / (n : ℝ)) * (-Real.log (n * w i) + n * w i - 1) ≤ ρ / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hw0, hw1, hdiv⟩ := hw
  have hdiv' : ∑ i : Fin n, (((1 : ℝ) / n : ℝ) : EReal) *
      EmpiricalDRO.Coverage.burg (w i / ((1 : ℝ) / n)) ≤ ((ρ / n : ℝ) : EReal) := hdiv
  have hterm : ∀ i : Fin n, 0 ≤ (((1 : ℝ) / n : ℝ) : EReal) *
      EmpiricalDRO.Coverage.burg (w i / ((1 : ℝ) / n)) := fun i =>
    mul_nonneg (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / n)) (edc_burg_nonneg _)
  have hpos : ∀ i, 0 < w i := by
    intro i
    by_contra hcon
    have hz : w i = 0 := le_antisymm (not_lt.mp hcon) (hw0 i)
    have h1 : (((1 : ℝ) / n : ℝ) : EReal) *
        EmpiricalDRO.Coverage.burg (w i / ((1 : ℝ) / n)) = ⊤ := by
      have : EmpiricalDRO.Coverage.burg (w i / ((1 : ℝ) / n)) = ⊤ := by
        simp [EmpiricalDRO.Coverage.burg, hz]
      rw [this]
      exact EReal.coe_mul_top_of_pos (by positivity)
    have h2 := Finset.single_le_sum (f := fun i : Fin n => (((1 : ℝ) / n : ℝ) : EReal) *
      EmpiricalDRO.Coverage.burg (w i / ((1 : ℝ) / n))) (fun j _ => hterm j) (Finset.mem_univ i)
    rw [h1] at h2
    have := le_trans h2 hdiv'
    exact absurd this (by simp)
  refine ⟨hpos, ?_⟩
  have hform : ∀ i : Fin n, (((1 : ℝ) / n : ℝ) : EReal) *
      EmpiricalDRO.Coverage.burg (w i / ((1 : ℝ) / n)) =
      (((1 : ℝ) / n * (-Real.log (n * w i) + n * w i - 1) : ℝ) : EReal) := by
    intro i
    have e : w i / ((1 : ℝ) / n) = n * w i := by field_simp
    have hp : 0 < w i / ((1 : ℝ) / n) := by positivity [hpos i]
    simp only [EmpiricalDRO.Coverage.burg, hp, if_true]
    rw [e, ← EReal.coe_mul]
  simp only [hform] at hdiv'
  rw [edc_coe_sum] at hdiv'
  exact_mod_cast hdiv'

lemma edc_log_bound (u : ℝ) (hu : u ≤ 1 / 2) : -(u + 2 * u ^ 2) ≤ Real.log (1 - u) := by
  have h1 : 0 < 1 - u := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : -(u + 2 * u ^ 2) ≤ 1 - (1 - u)⁻¹ := by
    have : (1 - u)⁻¹ ≤ 1 + u + 2 * u ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ h1]
      nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (by linarith : (0 : ℝ) ≤ 1 - 2 * u)]
    linarith
  linarith

lemma edc_pointwise (s u : ℝ) (hs : 0 < s) (hu : u ≤ 1 / 2) :
    s * u ≤ (-Real.log s + s - 1) + (u + 2 * u ^ 2) := by
  have h1 : 0 < 1 - u := by linarith
  have h2 := Real.log_le_sub_one_of_pos (mul_pos hs h1)
  rw [Real.log_mul hs.ne' h1.ne'] at h2
  have h3 := edc_log_bound u hu
  nlinarith

theorem solution {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ q lam : ℝ) (hq : 0 ≤ q)
    (hlam : 0 < lam) (hmax : ∀ i, |z i - μ| ≤ lam / 2) :
    GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) z - μ ≤
      (1 / (n : ℝ)) * ∑ i, (z i - μ) + 2 * ((1 / (n : ℝ)) * ∑ i, (z i - μ) ^ 2) / lam +
        lam * (q / (2 * n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem0 : (fun _ : Fin n => (1 : ℝ) / n) ∈
      PhiDivRobust.Counterpart.probUncertaintySet EmpiricalDRO.Coverage.burg
        (fun _ => (1 : ℝ) / n) ((q / 2) / n) := by
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
      exact_mod_cast (by positivity : (0 : ℝ) ≤ (q / 2) / n)
  unfold GenEmpLik.Expansion.robustMean
  have key : ∀ w ∈ PhiDivRobust.Counterpart.probUncertaintySet EmpiricalDRO.Coverage.burg
        (fun _ => (1 : ℝ) / n) ((q / 2) / n),
      ∑ i, w i * z i - μ ≤ (1 / (n : ℝ)) * ∑ i, (z i - μ) +
        2 * ((1 / (n : ℝ)) * ∑ i, (z i - μ) ^ 2) / lam + lam * (q / (2 * n)) := by
    intro w hw
    obtain ⟨hpos, hdiv⟩ := edc_ball hn (q / 2) w hw
    have hw1 : ∑ i, w i = 1 := hw.2.1
    have hsum : ∑ i, w i * z i - μ = ∑ i, w i * (z i - μ) := by
      have : ∑ i, w i * (z i - μ) = ∑ i, w i * z i - μ * ∑ i, w i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [this, hw1]; ring
    -- pointwise bound
    have hpt : ∀ i, w i * (z i - μ) ≤
        lam * ((1 / (n : ℝ)) * (-Real.log (n * w i) + n * w i - 1)) +
          (1 / (n : ℝ)) * ((z i - μ) + 2 * (z i - μ) ^ 2 / lam) := by
      intro i
      have hu : (z i - μ) / lam ≤ 1 / 2 := by
        rw [div_le_iff₀ hlam]
        have := (abs_le.mp (hmax i)).2
        linarith
      have h := edc_pointwise (n * w i) ((z i - μ) / lam) (by have := hpos i; positivity) hu
      have h2 : lam * (1 / (n : ℝ)) * (n * w i * ((z i - μ) / lam)) = w i * (z i - μ) := by
        field_simp
      have h3 : lam * (1 / (n : ℝ)) * (((z i - μ) / lam) + 2 * ((z i - μ) / lam) ^ 2) =
          (1 / (n : ℝ)) * ((z i - μ) + 2 * (z i - μ) ^ 2 / lam) := by
        field_simp
      have hc : 0 ≤ lam * (1 / (n : ℝ)) := by positivity
      have := mul_le_mul_of_nonneg_left h hc
      calc w i * (z i - μ) = lam * (1 / (n : ℝ)) * (n * w i * ((z i - μ) / lam)) := h2.symm
        _ ≤ lam * (1 / (n : ℝ)) * ((-Real.log (n * w i) + n * w i - 1) +
              ((z i - μ) / lam + 2 * ((z i - μ) / lam) ^ 2)) := this
        _ = _ := by rw [mul_add, h3]; ring
    have hsumle := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
    rw [Finset.sum_add_distrib] at hsumle
    simp only [← Finset.mul_sum] at hsumle hdiv
    have e1 : ∑ i, ((z i - μ) + 2 * (z i - μ) ^ 2 / lam) =
        ∑ i, (z i - μ) + 2 * (∑ i, (z i - μ) ^ 2) / lam := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    rw [e1] at hsumle
    have e2 : 1 / (n : ℝ) * (∑ i, (z i - μ) + 2 * (∑ i, (z i - μ) ^ 2) / lam) =
        (1 / (n : ℝ)) * ∑ i, (z i - μ) + 2 * ((1 / (n : ℝ)) * ∑ i, (z i - μ) ^ 2) / lam := by
      field_simp
    have e3 : lam * (q / 2 / n) = lam * (q / (2 * n)) := by
      field_simp
    have := mul_le_mul_of_nonneg_left hdiv hlam.le
    rw [hsum]
    rw [e2] at hsumle
    linarith
  rw [sub_le_iff_le_add]
  refine csSup_le ⟨_, _, hmem0, rfl⟩ ?_
  rintro _ ⟨w, hw, rfl⟩
  have := key w hw
  linarith
