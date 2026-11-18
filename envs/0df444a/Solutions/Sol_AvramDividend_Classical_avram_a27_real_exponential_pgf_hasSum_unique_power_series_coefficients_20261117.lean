-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T21:03:20.298215+00:00
-- url     : https://prove2.me/submissions/9a9c1fd0-8daa-421f-a8e2-b7263aa12997

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
noncomputable section

namespace PgfAux

lemma bdd_of_summable (a : ℕ → ℝ) (h : Summable a) : ∃ M, 0 ≤ M ∧ ∀ i, |a i| ≤ M := by
  have ht : Tendsto (fun i => |a i|) atTop (nhds 0) := by
    simpa using (h.tendsto_atTop_zero).abs
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  refine ⟨max M 0, le_max_right _ _, fun i => le_trans (hM ⟨i, rfl⟩) (le_max_left _ _)⟩

lemma coeff_zero (a : ℕ → ℝ)
    (h : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → HasSum (fun k : ℕ => z ^ k * a k) 0) : ∀ k, a k = 0 := by
  obtain ⟨M, hM0, hM⟩ := bdd_of_summable a (by simpa using (h 1 zero_le_one le_rfl).summable)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have key : ∀ z : ℝ, 0 < z → z ≤ 1/2 → |a k| ≤ 2 * M * z := by
      intro z hz hz2
      have hs := h z hz.le (by linarith)
      have h1 := (hasSum_nat_add_iff' (k+1)).mpr hs
      have hfin : ∑ i ∈ Finset.range (k+1), z ^ i * a i = z ^ k * a k := by
        rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
          rw [ih i (Finset.mem_range.mp hi), mul_zero]), zero_add]
      rw [hfin] at h1
      have hzk : 0 < z ^ k := pow_pos hz k
      have h2 : HasSum (fun i => z ^ (i+1) * a (i + (k+1))) (-(a k)) := by
        have := h1.mul_left (1 / z ^ k)
        have e1 : (fun i => z ^ (i+1) * a (i + (k+1))) =
            fun i => 1 / z ^ k * (z ^ (i + (k + 1)) * a (i + (k + 1))) := by
          funext i; rw [pow_add, pow_succ]; field_simp; ring
        have e2 : -(a k) = 1 / z ^ k * (0 - z ^ k * a k) := by rw [zero_sub]; field_simp
        rw [e1, e2]; exact this
      have hg : HasSum (fun i : ℕ => z ^ (i+1) * M) (z * M / (1 - z)) := by
        have := (hasSum_geometric_of_lt_one hz.le (by linarith)).mul_left (z * M)
        have e1 : (fun i : ℕ => z ^ (i+1) * M) = fun i => z * M * z ^ i := by
          funext i; ring
        have hz1 : (1 - z) ≠ 0 := by linarith
        have e2 : z * M / (1 - z) = z * M * (1 - z)⁻¹ := by rw [div_eq_mul_inv]
        rw [e1, e2]; exact this
      have hb : ∀ i, |z ^ (i+1) * a (i + (k+1))| ≤ z ^ (i+1) * M := by
        intro i
        rw [abs_mul, abs_of_pos (pow_pos hz _)]
        exact mul_le_mul_of_nonneg_left (hM _) (pow_pos hz _).le
      have u1 : -(a k) ≤ z * M / (1 - z) := hasSum_le (fun i => (abs_le.mp (hb i)).2) h2 hg
      have u2 : -(z * M / (1 - z)) ≤ -(a k) :=
        hasSum_le (fun i => by simpa using (abs_le.mp (hb i)).1) hg.neg h2
      have hzM : z * M / (1 - z) ≤ 2 * M * z := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [mul_nonneg (mul_nonneg hz.le hM0) (by linarith : (0:ℝ) ≤ 1/2 - z)]
      rw [abs_le]; constructor <;> linarith
    by_contra hne
    have ht : 0 < |a k| := abs_pos.mpr hne
    set z := min (1/2 : ℝ) (|a k| / (4 * M + 4)) with hzdef
    have hz : 0 < z := lt_min (by norm_num) (div_pos ht (by linarith))
    have hz2 : z ≤ 1/2 := min_le_left _ _
    have hz3 : z ≤ |a k| / (4 * M + 4) := min_le_right _ _
    have := key z hz hz2
    have h4 : z * (4 * M + 4) ≤ |a k| := by rwa [le_div_iff₀ (by linarith)] at hz3
    nlinarith

lemma exp_hasSum (r q z : ℝ) :
    HasSum (fun k : ℕ => z ^ k * (Real.exp (-r) * q ^ k / (k.factorial : ℝ))) (Real.exp (q * z - r)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (q * z)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-r))
  have e : Real.exp (q * z - r) = Real.exp (-r) * Real.exp (q * z) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have e3 : (fun k : ℕ => z ^ k * (Real.exp (-r) * q ^ k / (k.factorial : ℝ))) =
      fun i => Real.exp (-r) * ((q * z) ^ i / (i.factorial : ℝ)) := by
    funext k; rw [mul_pow]; ring
  rw [e3]; exact h2

lemma main (C : ℕ → ℝ) (r q : ℝ)
    (hSeries : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k : ℕ => z ^ k * C k) (Real.exp (q * z - r))) :
    ∀ k : ℕ, C k = Real.exp (-r) * q ^ k / (k.factorial : ℝ) := by
  have := coeff_zero (fun k => C k - Real.exp (-r) * q ^ k / (k.factorial : ℝ)) (by
    intro z h0 h1
    have := (hSeries z h0 h1).sub (exp_hasSum r q z)
    rw [sub_self] at this
    have e3 : (fun k => z ^ k * (C k - Real.exp (-r) * q ^ k / (k.factorial : ℝ))) =
        fun b => z ^ b * C b - z ^ b * (Real.exp (-r) * q ^ b / (b.factorial : ℝ)) := by
      funext k; ring
    rw [e3]; exact this)
  intro k; linarith [this k]

end PgfAux

theorem solution
    (C : ℕ → ℝ) (r q : ℝ)
    (hSeries : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k : ℕ => z ^ k * C k) (Real.exp (q * z - r))) :
    ∀ k : ℕ, C k = Real.exp (-r) * q ^ k / (k.factorial : ℝ) :=
  PgfAux.main C r q hSeries
