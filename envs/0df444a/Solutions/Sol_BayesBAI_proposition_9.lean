-- Prove2me | solution 1 for BayesBAI.proposition_9
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:57:38.162515+00:00
-- url     : https://prove2.me/submissions/1c9b36ad-4978-4d0a-8362-a70e89ee457a

import Mathlib

open Real Filter Topology Stirling

lemma term_le (r : ℝ) (hr : 0 < r) (j : ℕ) :
    1 / (2 * ((j:ℝ) + 1) + 1) * r ^ (j + 1) ≤ r ^ (j + 1) / 3 := by
  have h : 0 < r ^ (j + 1) := by positivity
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  rw [div_mul_eq_mul_div, one_mul]
  apply div_le_div_of_nonneg_left h.le (by norm_num)
  linarith

lemma term_lt (r : ℝ) (hr : 0 < r) :
    1 / (2 * (((1:ℕ):ℝ) + 1) + 1) * r ^ (1 + 1) < r ^ (1 + 1) / 3 := by
  have h : 0 < r ^ (1 + 1) := by positivity
  norm_num
  nlinarith

lemma three_pow (j : ℕ) : (2 * ((j:ℝ) + 1) + 1) ≤ 3 ^ (j + 1) := by
  have : (2 * j + 3 : ℕ) ≤ 3 ^ (j + 1) := by
    induction j with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  have h2 : ((2 * j + 3 : ℕ) : ℝ) ≤ ((3 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at h2; linarith

lemma term_ge (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (r / 3) ^ (j + 1) ≤ 1 / (2 * ((j:ℝ) + 1) + 1) * r ^ (j + 1) := by
  have h : 0 < r ^ (j + 1) := by positivity
  rw [div_pow, div_mul_eq_mul_div, one_mul]
  apply div_le_div_of_nonneg_left h.le (by positivity) (three_pow j)

lemma term_gt (r : ℝ) (hr : 0 < r) :
    (r / 3) ^ (1 + 1) < 1 / (2 * (((1:ℕ):ℝ) + 1) + 1) * r ^ (1 + 1) := by
  have h : 0 < r ^ (1 + 1) := by positivity
  norm_num
  nlinarith

lemma series (m : ℕ) : HasSum (fun k : ℕ => 1 / (2 * ((k:ℝ) + 1) + 1) *
      (((1 : ℝ) / (2 * ((m:ℝ) + 1) + 1)) ^ 2) ^ (k + 1))
    (log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2))) := by
  have := log_stirlingSeq_sdiff_hasSum m
  push_cast at this
  exact this

lemma r_bounds (m : ℕ) : 0 < ((1 : ℝ) / (2 * ((m:ℝ) + 1) + 1)) ^ 2 ∧
    ((1 : ℝ) / (2 * ((m:ℝ) + 1) + 1)) ^ 2 ≤ 1 / 9 := by
  constructor
  · positivity
  · have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have h3 : (3:ℝ) ≤ 2 * ((m:ℝ) + 1) + 1 := by linarith
    rw [div_pow, one_pow]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith

/-- strict upper step -/
lemma d_lt (m : ℕ) :
    log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2)) < 1 / (12 * ((m:ℝ) + 1) * ((m:ℝ) + 2)) := by
  obtain ⟨hr0, hr9⟩ := r_bounds m
  set r : ℝ := ((1 : ℝ) / (2 * ((m:ℝ) + 1) + 1)) ^ 2 with hr
  have hr1 : r < 1 := by linarith
  have hG : HasSum (fun j : ℕ ↦ r ^ (j + 1) / 3) (r / (1 - r) / 3) := by
    have := ((hasSum_geometric_of_lt_one hr0.le hr1).mul_left r).div_const 3
    have e : (fun j : ℕ ↦ r ^ (j + 1) / 3) = fun i => r * r ^ i / 3 := by funext j; ring
    rw [e, show r / (1 - r) / 3 = r * (1 - r)⁻¹ / 3 by ring]; exact this
  have hval : r / (1 - r) / 3 = 1 / (12 * ((m:ℝ) + 1) * ((m:ℝ) + 2)) := by
    have hd : (1:ℝ) - r = 4 * ((m:ℝ) + 1) * ((m:ℝ) + 2) / (2 * ((m:ℝ) + 1) + 1) ^ 2 := by
      rw [hr]; field_simp; ring
    rw [hd, hr]; field_simp; ring
  rw [← hval]
  exact hasSum_lt (fun j => term_le r hr0 j) (term_lt r hr0) (series m) hG

/-- lower step -/
lemma d_gt (m : ℕ) :
    1 / (12 * ((m:ℝ) + 1) + 1) - 1 / (12 * ((m:ℝ) + 2) + 1) <
      log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2)) := by
  obtain ⟨hr0, hr9⟩ := r_bounds m
  set r : ℝ := ((1 : ℝ) / (2 * ((m:ℝ) + 1) + 1)) ^ 2 with hr
  have hq0 : 0 ≤ r / 3 := by positivity
  have hq1 : r / 3 < 1 := by linarith
  have hG : HasSum (fun j : ℕ ↦ (r / 3) ^ (j + 1)) ((r / 3) / (1 - r / 3)) := by
    have := ((hasSum_geometric_of_lt_one hq0 hq1).mul_left (r / 3))
    have e : (fun j : ℕ ↦ (r / 3) ^ (j + 1)) = fun i => r / 3 * (r / 3) ^ i := by funext j; ring
    rw [e, div_eq_mul_inv (r / 3)]; exact this
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hle : 1 / (12 * ((m:ℝ) + 1) + 1) - 1 / (12 * ((m:ℝ) + 2) + 1) ≤ (r / 3) / (1 - r / 3) := by
    have hpos : (0:ℝ) < 3 * (2 * ((m:ℝ) + 1) + 1) ^ 2 - 1 := by nlinarith
    have e : (r / 3) / (1 - r / 3) = 1 / (3 * (2 * ((m:ℝ) + 1) + 1) ^ 2 - 1) := by
      have hd : (1:ℝ) - r / 3 = (3 * (2 * ((m:ℝ) + 1) + 1) ^ 2 - 1) / (3 * (2 * ((m:ℝ) + 1) + 1) ^ 2) := by
        rw [hr]; field_simp
      rw [hd, hr]; field_simp
    rw [e, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hpos]
    nlinarith
  exact lt_of_le_of_lt hle (hasSum_lt (fun j => term_ge r hr0 j) (term_gt r hr0) hG (series m))

lemma tend_log (n : ℕ) : Tendsto (fun k : ℕ => log (stirlingSeq (n + 1 + k))) atTop
    (𝓝 (log (Real.sqrt π))) := by
  have h1 : Tendsto (fun k : ℕ => stirlingSeq (n + 1 + k)) atTop (𝓝 (Real.sqrt π)) :=
    tendsto_stirlingSeq_sqrt_pi.comp (tendsto_atTop_atTop_of_monotone
      (fun a b h => by omega) (fun b => ⟨b, by omega⟩))
  exact (Real.continuousAt_log (by positivity)).tendsto.comp h1

lemma upper_tail (n : ℕ) :
    log (stirlingSeq (n + 1)) - log (Real.sqrt π) ≤ 1 / (12 * ((n:ℝ) + 1)) := by
  have hk : ∀ k : ℕ, log (stirlingSeq (n + 1)) - log (stirlingSeq (n + 1 + k)) ≤
      1 / (12 * ((n:ℝ) + 1)) - 1 / (12 * ((n:ℝ) + 1 + k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := log_stirlingSeq_sdiff_le (n + 1 + k)
      push_cast at this ⊢
      have e : 1 / (12 * ((n:ℝ) + 1 + k) * ((n:ℝ) + 1 + k + 1)) =
          1 / (12 * ((n:ℝ) + 1 + k)) - 1 / (12 * ((n:ℝ) + 1 + (k + 1))) := by
        field_simp; ring
      rw [show n + 1 + (k + 1) = n + 1 + k + 1 by omega]
      have : (12 * ((n:ℝ) + 1 + ↑k) * ((n:ℝ) + 1 + ↑k + 1)) = 12 * (↑(n + 1 + k):ℝ) * (↑(n + 1 + k) + 1) := by
        push_cast; ring
      linarith
  have hlim := (tend_log n).const_sub (log (stirlingSeq (n + 1)))
  refine le_of_tendsto hlim (Eventually.of_forall (fun k => (hk k).trans ?_))
  have : 0 ≤ 1 / (12 * ((n:ℝ) + 1 + k)) := by positivity
  linarith

lemma lower_tail (n : ℕ) :
    1 / (12 * ((n:ℝ) + 1) + 1) ≤ log (stirlingSeq (n + 1)) - log (Real.sqrt π) := by
  have hk : ∀ k : ℕ, 1 / (12 * ((n:ℝ) + 1) + 1) - 1 / (12 * ((n:ℝ) + 1 + k) + 1) ≤
      log (stirlingSeq (n + 1)) - log (stirlingSeq (n + 1 + k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := d_gt (n + k)
      rw [show n + k + 1 = n + 1 + k by omega, show n + k + 2 = n + 1 + (k + 1) by omega] at this
      push_cast at this ⊢
      have e1 : ((n:ℝ) + (k:ℝ) + 1) = (n:ℝ) + 1 + k := by ring
      have e2 : ((n:ℝ) + (k:ℝ) + 2) = (n:ℝ) + 1 + (k + 1) := by ring
      rw [e1, e2] at this
      linarith
  have hlim := (tend_log n).const_sub (log (stirlingSeq (n + 1)))
  have hl2 : Tendsto (fun k : ℕ => 1 / (12 * ((n:ℝ) + 1) + 1) - 1 / (12 * ((n:ℝ) + 1 + k) + 1))
      atTop (𝓝 (1 / (12 * ((n:ℝ) + 1) + 1) - 0)) := by
    apply Tendsto.const_sub
    apply Tendsto.div_atTop tendsto_const_nhds
    apply tendsto_atTop_add_const_right
    apply Tendsto.const_mul_atTop (by norm_num)
    apply tendsto_atTop_add_const_left
    exact tendsto_natCast_atTop_atTop
  rw [sub_zero] at hl2
  exact le_of_tendsto_of_tendsto hl2 hlim (Eventually.of_forall hk)

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * Real.pi) * (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) *
        Real.exp (1 / (12 * (n : ℝ) + 1)) < (n.factorial : ℝ) ∧
    (n.factorial : ℝ) < Real.sqrt (2 * Real.pi) * (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) *
        Real.exp (1 / (12 * (n : ℝ))) ∧
    Real.sqrt (2 * Real.pi) * (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) <
        (n.factorial : ℝ) ∧
    (n.factorial : ℝ) < Real.sqrt (2 * Real.pi) * (n : ℝ) ^ ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) *
        (1 + 1 / (6 * (n : ℝ))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set A : ℝ := Real.sqrt (2 * Real.pi) * ((m + 1 : ℕ) : ℝ) ^ (((m + 1 : ℕ) : ℝ) + 1 / 2) *
    Real.exp (-((m + 1 : ℕ) : ℝ)) with hA
  have hn0 : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hA0 : 0 < A := by positivity
  set L : ℝ := log (stirlingSeq (m + 1)) - log (Real.sqrt π) with hL
  have hs0 : 0 < stirlingSeq (m + 1) := stirlingSeq'_pos m
  have hfac : ((m + 1).factorial : ℝ) = A * Real.exp L := by
    have hAeq : A = Real.sqrt π * (Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) *
        (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) := by
      rw [hA, Real.rpow_add hn0, Real.rpow_natCast, div_pow, Real.exp_one_pow, Real.exp_neg,
        Real.sqrt_mul' _ hn0.le, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_eq_rpow π,
        Real.sqrt_eq_rpow 2, Real.sqrt_eq_rpow (((m + 1 : ℕ) : ℝ))]
      push_cast
      field_simp
    have hexpL : Real.exp L = stirlingSeq (m + 1) / Real.sqrt π := by
      rw [hL, Real.exp_sub, Real.exp_log hs0, Real.exp_log (by positivity)]
    rw [hexpL, hAeq, stirlingSeq]
    have : 0 < Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) * (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by
      positivity
    have : 0 < Real.sqrt π := by positivity
    field_simp
  -- the two bounds on L
  have hup : L < 1 / (12 * ((m + 1 : ℕ) : ℝ)) := by
    have h1 := d_lt m
    have h2 := upper_tail (m + 1)
    have : L = (log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2))) +
      (log (stirlingSeq (m + 1 + 1)) - log (Real.sqrt π)) := by rw [hL]; ring
    rw [this]
    push_cast at h2 ⊢
    have e : 1 / (12 * ((m:ℝ) + 1) * ((m:ℝ) + 2)) + 1 / (12 * ((m:ℝ) + 1 + 1)) =
        1 / (12 * ((m:ℝ) + 1)) := by field_simp; ring
    linarith
  have hlow : 1 / (12 * ((m + 1 : ℕ) : ℝ) + 1) < L := by
    have h1 := d_gt m
    have h2 := lower_tail (m + 1)
    have : L = (log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2))) +
      (log (stirlingSeq (m + 1 + 1)) - log (Real.sqrt π)) := by rw [hL]; ring
    rw [this]
    push_cast at h2 ⊢
    have e : ((m:ℝ) + 1 + 1) = (m:ℝ) + 2 := by ring
    rw [e] at h2
    linarith
  rw [hfac]
  have hLpos : 0 < L := lt_trans (by positivity) hlow
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hlow) hA0
  · exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hup) hA0
  · have := Real.one_lt_exp_iff.mpr hLpos  -- placeholder name
    nlinarith
  · apply mul_lt_mul_of_pos_left _ hA0
    have hy : |1 / (12 * ((m + 1 : ℕ) : ℝ))| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one (by positivity)]
      have : (1:ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      linarith
    have hb := Real.abs_exp_sub_one_le hy
    rw [abs_of_pos (by positivity : (0:ℝ) < 1 / (12 * ((m + 1 : ℕ) : ℝ)))] at hb
    have hle := (abs_le.mp hb).2
    have hexp : Real.exp L < Real.exp (1 / (12 * ((m + 1 : ℕ) : ℝ))) := Real.exp_lt_exp.mpr hup
    have e : 2 * (1 / (12 * ((m + 1 : ℕ) : ℝ))) = 1 / (6 * ((m + 1 : ℕ) : ℝ)) := by
      field_simp; ring
    linarith
