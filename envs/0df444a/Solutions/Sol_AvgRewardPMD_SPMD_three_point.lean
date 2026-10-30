-- Prove2me | solution 1 for AvgRewardPMD.SPMD.three_point
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T11:28:05.600176+00:00
-- url     : https://prove2.me/submissions/35d8f02e-2dea-44c4-beea-35041d419f1e

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

open AvgRewardPMD.SPMD Filter Topology

namespace SPMDThreePointAux

lemma mul_log_div (z q : ℝ) (hq : q ≠ 0) : z * Real.log (z / q) = z * Real.log z - z * Real.log q := by
  rcases eq_or_ne z 0 with h | h
  · simp [h]
  · rw [Real.log_div h hq]; ring

lemma kl_eq {A : Type*} [Fintype A] (p q : A → ℝ) (hq : ∀ a, 0 < q a) :
    kl p q = ∑ a, p a * Real.log (p a) - ∑ a, p a * Real.log (q a) := by
  unfold kl
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => mul_log_div _ _ (hq a).ne'

lemma psi_convex (qa x y t : ℝ) (hq : 0 < qa) (hx : 0 ≤ x) (hy : 0 ≤ y) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ((1-t)*x + t*y) * Real.log (((1-t)*x + t*y)/qa)
      ≤ (1-t) * (x * Real.log (x/qa)) + t * (y * Real.log (y/qa)) := by
  rw [mul_log_div _ _ hq.ne', mul_log_div _ _ hq.ne', mul_log_div _ _ hq.ne']
  have h := (Real.convexOn_mul_log).2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy)
    (show 0 ≤ 1 - t by linarith) ht0 (by ring)
  simp only [smul_eq_mul] at h
  nlinarith [h]

lemma kl_nonneg'' {A : Type*} [Fintype A] (p r : A → ℝ) (hp : p ∈ stdSimplex ℝ A)
    (hr : ∀ a, 0 < r a) (hrs : ∑ a, r a = 1) : 0 ≤ kl p r := by
  have key : ∀ a, p a - r a ≤ p a * Real.log (p a / r a) := by
    intro a
    rcases (hp.1 a).eq_or_lt with h0 | hx
    · rw [← h0]; simp; linarith [hr a]
    · have ht : 0 < p a / r a := div_pos hx (hr a)
      have h := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
      rw [Real.log_inv] at h
      have hy' : r a ≠ 0 := (hr a).ne'
      have hx' : p a ≠ 0 := hx.ne'
      calc p a - r a = p a * (1 - (p a / r a)⁻¹) := by field_simp
        _ ≤ p a * Real.log (p a / r a) := mul_le_mul_of_nonneg_left (by linarith) hx.le
  unfold kl
  have : ∑ a, (p a - r a) ≤ ∑ a, p a * Real.log (p a / r a) :=
    Finset.sum_le_sum fun a _ => key a
  rw [Finset.sum_sub_distrib, hp.2, hrs] at this
  linarith

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- the minimizer of the KL prox step is strictly positive -/
lemma qplus_pos (H : (A → ℝ) → ℝ) (ω lam : ℝ)
    (hH : IsKLStrongConvexOn H ω) (hlam : 0 ≤ lam) (Q q qplus : A → ℝ)
    (hq : q ∈ stdSimplex ℝ A) (hqpos : ∀ a, 0 < q a) (hqplus : qplus ∈ stdSimplex ℝ A)
    (hmin : ∀ p ∈ stdSimplex ℝ A,
      lam * (∑ a, Q a * qplus a + H qplus) + kl qplus q ≤ lam * (∑ a, Q a * p a + H p) + kl p q) :
    ∀ a, 0 < qplus a := by
  intro a0
  rcases (hqplus.1 a0).eq_or_lt with h0 | h
  swap; · exact h
  exfalso
  set ψ : A → ℝ → ℝ := fun a x => x * Real.log (x / q a) with hψ
  set C2 := ∑ a ∈ Finset.univ.erase a0, (ψ a (q a) - ψ a (qplus a)) with hC2
  set C := lam * ∑ a, Q a * (q a - qplus a) + lam * (H q - H qplus) + C2 with hC
  have hq0 := hqpos a0
  have bound : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ C + q a0 * Real.log t := by
    intro t ht0 ht1
    set pt : A → ℝ := (1 - t) • qplus + t • q with hpt
    have hpta : ∀ a, pt a = (1 - t) * qplus a + t * q a := fun a => by
      simp [pt, smul_eq_mul]
    have hptS : pt ∈ stdSimplex ℝ A :=
      (convex_stdSimplex ℝ A) hqplus hq (by linarith) ht0.le (by ring)
    have hHc := hH.2.1.2 hqplus hq (show 0 ≤ 1 - t by linarith) ht0.le (by ring)
    simp only [smul_eq_mul] at hHc
    rw [← hpt] at hHc
    have hm := hmin pt hptS
    -- linear part
    have hlin : ∑ a, Q a * pt a = ∑ a, Q a * qplus a + t * ∑ a, Q a * (q a - qplus a) := by
      simp_rw [hpta, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    -- kl part
    have hkl : kl pt q - kl qplus q ≤ t * C2 + t * q a0 * Real.log t := by
      unfold kl
      rw [← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
      have e0 : pt a0 * Real.log (pt a0 / q a0) - qplus a0 * Real.log (qplus a0 / q a0)
          = t * q a0 * Real.log t := by
        rw [hpta, ← h0]
        simp only [mul_zero, zero_add, zero_mul, zero_div, Real.log_zero, sub_zero]
        rw [mul_div_assoc, div_self hq0.ne', mul_one]
      rw [e0, hC2, Finset.mul_sum]
      have : ∑ x ∈ Finset.univ.erase a0, (pt x * Real.log (pt x / q x) - qplus x * Real.log (qplus x / q x))
          ≤ ∑ x ∈ Finset.univ.erase a0, t * (ψ x (q x) - ψ x (qplus x)) := by
        apply Finset.sum_le_sum; intro a _
        simp only [ψ]
        rw [hpta]
        have := psi_convex (q a) (qplus a) (q a) t (hqpos a) (hqplus.1 a) (hq.1 a) ht0.le ht1
        linarith
      linarith
    have hHt := mul_le_mul_of_nonneg_left hHc hlam
    rw [hlin] at hm
    have : 0 ≤ t * (C + q a0 * Real.log t) := by
      simp only [hC]
      nlinarith
    exact (mul_nonneg_iff_of_pos_left ht0).1 this
  set t := Real.exp (-(|C| + 1) / q a0)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by
    apply Real.exp_le_one_iff.2
    apply div_nonpos_of_nonpos_of_nonneg _ hq0.le
    linarith [abs_nonneg C]
  have := bound t ht0 ht1
  rw [Real.log_exp, mul_div_cancel₀ _ hq0.ne'] at this
  linarith [le_abs_self C]

end SPMDThreePointAux

open SPMDThreePointAux in
theorem solution {A : Type*} [Fintype A] [DecidableEq A] (H : (A → ℝ) → ℝ) (ω lam : ℝ)
    (hH : IsKLStrongConvexOn H ω) (hlam : 0 ≤ lam) (Q q qplus : A → ℝ)
    (hq : q ∈ stdSimplex ℝ A) (hqpos : ∀ a, 0 < q a) (hqplus : qplus ∈ stdSimplex ℝ A)
    (hmin : ∀ p ∈ stdSimplex ℝ A,
      lam * (∑ a, Q a * qplus a + H qplus) + kl qplus q ≤ lam * (∑ a, Q a * p a + H p) + kl p q) :
    ∀ p ∈ stdSimplex ℝ A,
      lam * (∑ a, Q a * (qplus a - p a) + H qplus - H p) + kl qplus q
        ≤ kl p q - (1 + lam * ω) * kl p qplus := by
  intro p hp
  have hqp := qplus_pos H ω lam hH hlam Q q qplus hq hqpos hqplus hmin
  set d : A → ℝ := fun a => p a - qplus a with hd
  set pt : ℝ → A → ℝ := fun t a => qplus a + t * d a with hpt
  have hω : 0 ≤ ω := hH.1
  have hineq : ∀ t : ℝ, 0 < t → t < 1 →
      0 ≤ lam * ∑ a, Q a * d a + lam * (H p - H qplus) - lam * ω * kl p (pt t)
          + t⁻¹ * (kl (pt t) q - kl qplus q) := by
    intro t ht0 ht1
    have hpta : ∀ a, pt t a = (1 - t) * qplus a + t * p a := fun a => by
      simp only [pt, d]; ring
    have hptv : pt t = (1 - t) • qplus + t • p := by
      funext a; rw [hpta]; simp [smul_eq_mul]
    have hptS : pt t ∈ stdSimplex ℝ A := by
      rw [hptv]; exact (convex_stdSimplex ℝ A) hqplus hp (by linarith) ht0.le (by ring)
    have hptpos : ∀ a, 0 < pt t a := fun a => by
      rw [hpta]
      have h1 : 0 < (1 - t) * qplus a := mul_pos (by linarith) (hqp a)
      have h2 : 0 ≤ t * p a := mul_nonneg ht0.le (hp.1 a)
      linarith
    obtain ⟨g, hg⟩ := hH.2.2 (pt t) hptS hptpos
    have h1 := hg qplus hqplus
    have h2 := hg p hp
    have hcomb : (1 - t) * ∑ a, g a * (qplus a - pt t a) + t * ∑ a, g a * (p a - pt t a) = 0 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero; intro a _
      rw [hpta]; ring
    have hkl0 : 0 ≤ kl qplus (pt t) := kl_nonneg'' _ _ hqplus hptpos hptS.2
    have h1' := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 - t by linarith)
    have h2' := mul_le_mul_of_nonneg_left h2 ht0.le
    have hωk : 0 ≤ (1 - t) * (ω * kl qplus (pt t)) :=
      mul_nonneg (by linarith) (mul_nonneg hω hkl0)
    -- E1 : ω t kl p pt ≤ (1-t) H q+ + t H p - H pt
    have E1 : t * (ω * kl p (pt t)) ≤ (1 - t) * H qplus + t * H p - H (pt t) := by
      nlinarith
    have hm := hmin (pt t) hptS
    have hlin : ∑ a, Q a * pt t a = ∑ a, Q a * qplus a + t * ∑ a, Q a * d a := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by simp only [pt]; ring
    rw [hlin] at hm
    have E1' := mul_le_mul_of_nonneg_left E1 hlam
    have key : 0 ≤ t * (lam * ∑ a, Q a * d a + lam * (H p - H qplus) - lam * ω * kl p (pt t))
        + (kl (pt t) q - kl qplus q) := by
      nlinarith
    have : lam * ∑ a, Q a * d a + lam * (H p - H qplus) - lam * ω * kl p (pt t)
          + t⁻¹ * (kl (pt t) q - kl qplus q)
        = t⁻¹ * (t * (lam * ∑ a, Q a * d a + lam * (H p - H qplus) - lam * ω * kl p (pt t))
        + (kl (pt t) q - kl qplus q)) := by
      field_simp
    rw [this]
    exact mul_nonneg (inv_nonneg.2 ht0.le) key
  have hpt0 : pt 0 = qplus := by funext a; simp [pt]
  -- continuity of t ↦ kl p (pt t) at 0
  have hF1 : ContinuousAt (fun t => kl p (pt t)) 0 := by
    unfold kl
    refine tendsto_finset_sum _ fun a _ => ?_
    rcases eq_or_ne (p a) 0 with h0 | h0
    · simp only [h0, zero_mul]; exact continuousAt_const
    · have hne : qplus a + 0 * d a ≠ 0 := by simp [(hqp a).ne']
      refine ContinuousAt.mul continuousAt_const (ContinuousAt.log ?_ ?_)
      · exact continuousAt_const.div (by fun_prop) hne
      · exact div_ne_zero h0 hne
  -- derivative of t ↦ kl (pt t) q at 0
  have hF2 : HasDerivAt (fun t => kl (pt t) q) (∑ a, d a * (Real.log (qplus a / q a) + 1)) 0 := by
    have hterm : ∀ a ∈ (Finset.univ : Finset A), HasDerivAt
        (fun t => (qplus a + t * d a) * Real.log ((qplus a + t * d a) / q a))
        (d a * (Real.log (qplus a / q a) + 1)) 0 := by
      intro a _
      have hu : HasDerivAt (fun t : ℝ => qplus a + t * d a) (1 * d a) 0 :=
        ((hasDerivAt_id (0:ℝ)).mul_const (d a)).const_add (qplus a)
      have hne : (qplus a + 0 * d a) / q a ≠ 0 := by
        simp [(hqp a).ne', (hqpos a).ne']
      have hl := (hu.div_const (q a)).log hne
      have := hu.mul hl
      refine this.congr_deriv ?_
      have hqa := (hqpos a).ne'
      have hqpa := (hqp a).ne'
      simp only [zero_mul, add_zero, one_mul]
      field_simp
    have := HasDerivAt.fun_sum hterm
    exact this
  have hslope := hF2.tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul] at hslope
  rw [hpt0] at hslope
  have hF1' : Tendsto (fun t => kl p (pt t)) (𝓝[>] 0) (𝓝 (kl p qplus)) := by
    have := hF1.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    rwa [hpt0] at this
  have hG := ((tendsto_const_nhds (x := lam * ∑ a, Q a * d a + lam * (H p - H qplus))).sub
    (hF1'.const_mul (lam * ω))).add hslope
  have hL : 0 ≤ lam * ∑ a, Q a * d a + lam * (H p - H qplus) - lam * ω * kl p qplus
      + ∑ a, d a * (Real.log (qplus a / q a) + 1) := by
    refine ge_of_tendsto hG ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    exact hineq t ht.1 ht.2
  have hid : ∑ a, d a * (Real.log (qplus a / q a) + 1) = kl p q - kl qplus q - kl p qplus := by
    rw [kl_eq p q hqpos, kl_eq qplus q hqpos, kl_eq p qplus hqp]
    have e : ∀ a, d a * (Real.log (qplus a / q a) + 1)
        = (p a * Real.log (qplus a) - qplus a * Real.log (qplus a))
          - (p a * Real.log (q a) - qplus a * Real.log (q a)) + (p a - qplus a) := by
      intro a
      rw [Real.log_div (hqp a).ne' (hqpos a).ne']
      simp only [d]; ring
    simp_rw [e]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp.2, hqplus.2]
    ring
  have hQd : ∑ a, Q a * (qplus a - p a) = -∑ a, Q a * d a := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by simp only [d]; ring
  rw [hid] at hL
  rw [hQd]
  nlinarith
