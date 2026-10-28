-- Prove2me | solution 1 for CompositeLB.DetLip.suboptimality_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:34:36.497311+00:00
-- url     : https://prove2.me/submissions/2e98f3ee-72b1-49a1-9f08-e16e1cc62d36

import Mathlib
import Definitions.Def_CompositeLB_DetLip_Model

namespace Aux_CLB_sb

open CompositeLB.DetLip

theorem hardmin {m d k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (b : ℝ) (v : ℕ → E d) (δ : Fin m → ℕ → ℝ)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v r))
    (hδ : ∀ i r, δ i r = 0 ∨ δ i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, δ i r = ((m / 2 : ℕ) : ℝ))
    (hb : b = 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) :
    let f : Fin m → E d → ℝ := fun i => hardF b k v (δ i)
    let xb : E d := b • ∑ r ∈ Finset.range (k + 1), v r
    (∀ x : E d,
      avgF f x = 1 / Real.sqrt 2 * |b - inner ℝ x (v 0)| +
        (((m / 2 : ℕ) : ℝ) / (2 * (m : ℝ) * Real.sqrt (k : ℝ))) *
          ∑ r ∈ Finset.Icc 1 k,
            |inner ℝ x (v (r - 1)) - inner ℝ x (v r)|) ∧
    (∀ x : E d, 0 ≤ avgF f x) ∧ avgF f xb = 0 ∧ ‖xb‖ = 1 := by
  intro f xb
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    exact this.ne'
  have hform : ∀ x : E d,
      avgF f x = 1 / Real.sqrt 2 * |b - inner ℝ x (v 0)| +
        (((m / 2 : ℕ) : ℝ) / (2 * (m : ℝ) * Real.sqrt (k : ℝ))) *
          ∑ r ∈ Finset.Icc 1 k, |inner ℝ x (v (r - 1)) - inner ℝ x (v r)| := by
    intro x
    unfold avgF
    simp only [f, hardF]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_comm]
    have e : ∑ r ∈ Finset.Icc 1 k, ∑ i : Fin m,
        δ i r * |inner ℝ x (v (r - 1)) - inner ℝ x (v r)|
        = ∑ r ∈ Finset.Icc 1 k, ((m / 2 : ℕ) : ℝ) * |inner ℝ x (v (r - 1)) - inner ℝ x (v r)| := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [← Finset.sum_mul, hsum r hr]
    rw [e, ← Finset.mul_sum]
    field_simp
  have hinner : ∀ r, r ≤ k → inner ℝ xb (v r) = b := by
    intro r hr
    simp only [xb]
    rw [inner_smul_left, sum_inner, Finset.sum_range (fun s => inner ℝ (v s) (v r))]
    have : ∑ s : Fin (k + 1), inner ℝ (v s) (v r) = 1 := by
      have h := fun s => (orthonormal_iff_ite.mp hv) s ⟨r, by omega⟩
      simp only at h
      rw [Finset.sum_congr rfl fun s _ => h s, Finset.sum_ite_eq']
      simp
    rw [this]
    simp
  refine ⟨hform, fun x => ?_, ?_, ?_⟩
  · rw [hform]
    have : 0 ≤ ((m / 2 : ℕ) : ℝ) / (2 * (m : ℝ) * Real.sqrt (k : ℝ)) := by positivity
    have : 0 ≤ ∑ r ∈ Finset.Icc 1 k, |inner ℝ x (v (r - 1)) - inner ℝ x (v r)| :=
      Finset.sum_nonneg fun r _ => abs_nonneg _
    positivity
  · rw [hform, hinner 0 (by omega), sub_self, abs_zero, mul_zero, zero_add]
    have : ∑ r ∈ Finset.Icc 1 k, |inner ℝ xb (v (r - 1)) - inner ℝ xb (v r)| = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      have hr' := Finset.mem_Icc.mp hr
      rw [hinner (r - 1) (by omega), hinner r hr'.2, sub_self, abs_zero]
    rw [this, mul_zero]
  · have hb2 : b ^ 2 * ((k : ℝ) + 1) = 1 := by
      rw [hb, div_pow, one_pow, Real.sq_sqrt (by positivity)]
      push_cast
      field_simp
    have hsq : ‖xb‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [show xb = b • ∑ r ∈ Finset.range (k + 1), v r from rfl]
      rw [inner_smul_right, inner_sum]
      rw [Finset.sum_congr rfl fun r hr => hinner r (by have := Finset.mem_range.mp hr; omega)]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      linarith [hb2]
    have h0 := norm_nonneg xb
    nlinarith

end Aux_CLB_sb

open CompositeLB.DetLip Aux_CLB_sb in
theorem solution {m d k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (b : ℝ) (v : ℕ → E d) (δ : Fin m → ℕ → ℝ)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v r))
    (hδ : ∀ i r, δ i r = 0 ∨ δ i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, δ i r = ((m / 2 : ℕ) : ℝ))
    (hb : b = 1 / Real.sqrt ((k + 1 : ℕ) : ℝ))
    (x xstar : E d)
    (hx : inner ℝ x (v k) = 0)
    (hstar_mem : xstar ∈ Metric.closedBall (0 : E d) 1)
    (hstar_min : ∀ y ∈ Metric.closedBall (0 : E d) 1,
      avgF (fun i => hardF b k v (δ i)) xstar ≤
        avgF (fun i => hardF b k v (δ i)) y) :
    b / (6 * Real.sqrt (k : ℝ)) ≤
        avgF (fun i => hardF b k v (δ i)) x -
          avgF (fun i => hardF b k v (δ i)) xstar ∧
      1 / (12 * (k : ℝ)) ≤ b / (6 * Real.sqrt (k : ℝ)) := by
  obtain ⟨hform, hnn, hxb0, hxb1⟩ := hardmin hm hk b v δ hv hδ hsum hb
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsk1 : 1 ≤ Real.sqrt (k : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hkr
  have hst : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hb0 : 0 < b := by rw [hb]; positivity
  -- the minimum value is zero
  have hstar0 : avgF (fun i => hardF b k v (δ i)) xstar = 0 := by
    have h1 := hstar_min (b • ∑ r ∈ Finset.range (k + 1), v r)
      (by rw [Metric.mem_closedBall, dist_zero_right, hxb1])
    rw [hxb0] at h1
    exact le_antisymm h1 (hnn xstar)
  refine ⟨?_, ?_⟩
  · rw [hstar0, sub_zero, hform x]
    set a : ℕ → ℝ := fun r => inner ℝ x (v r) with ha
    have hS : |a 0| ≤ ∑ r ∈ Finset.Icc 1 k, |inner ℝ x (v (r - 1)) - inner ℝ x (v r)| := by
      have htel : ∑ r ∈ Finset.Icc 1 k, (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) = a 0 := by
        have e : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := rfl
        rw [e, Finset.sum_Ico_eq_sum_range]
        have : ∀ i ∈ Finset.range (k + 1 - 1),
            (inner ℝ x (v (1 + i - 1)) - inner ℝ x (v (1 + i))) = a i - a (i + 1) := by
          intro i _
          simp only [ha]
          rw [show 1 + i - 1 = i by omega, show 1 + i = i + 1 by omega]
        rw [Finset.sum_congr rfl this, Finset.sum_range_sub', show k + 1 - 1 = k by omega]
        simp only [ha, hx, sub_zero]
      rw [← htel]
      exact Finset.abs_sum_le_sum_abs _ _
    have hC : 1 / (6 * Real.sqrt (k : ℝ)) ≤
        ((m / 2 : ℕ) : ℝ) / (2 * (m : ℝ) * Real.sqrt (k : ℝ)) := by
      have hm3 : (m : ℝ) ≤ 3 * ((m / 2 : ℕ) : ℝ) := by
        have : m ≤ 3 * (m / 2) := by omega
        exact_mod_cast this
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : 1 / (6 * Real.sqrt (k : ℝ)) ≤ 1 / Real.sqrt 2 := by
      apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num))
      have : Real.sqrt 2 ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    have hCnn : 0 ≤ 1 / (6 * Real.sqrt (k : ℝ)) := by positivity
    have t1 : 1 / (6 * Real.sqrt (k : ℝ)) * |b - a 0| ≤ 1 / Real.sqrt 2 * |b - inner ℝ x (v 0)| :=
      mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    have t2 : 1 / (6 * Real.sqrt (k : ℝ)) * |a 0| ≤
        ((m / 2 : ℕ) : ℝ) / (2 * (m : ℝ) * Real.sqrt (k : ℝ)) *
          ∑ r ∈ Finset.Icc 1 k, |inner ℝ x (v (r - 1)) - inner ℝ x (v r)| :=
      mul_le_mul hC hS (abs_nonneg _) (le_trans hCnn hC)
    have t3 : |b| ≤ |b - a 0| + |a 0| := by
      have := abs_add_le (b - a 0) (a 0); simpa using this
    rw [abs_of_pos hb0] at t3
    have : b / (6 * Real.sqrt (k : ℝ)) = 1 / (6 * Real.sqrt (k : ℝ)) * b := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left t3 hCnn]
  · rw [hb, div_div]
    apply one_div_le_one_div_of_le (by positivity)
    have hs2 : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt (by linarith)
    have ht2 : Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 = k + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have hprod : Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.sqrt (k : ℝ) ≤ 2 * k := by
      nlinarith [mul_pos hst hsk, sq_nonneg (Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.sqrt (k : ℝ) - 2 * k)]
    nlinarith
