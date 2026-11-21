-- Prove2me | solution 1 for CongestionApproxPNE.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:35:01.012933+00:00
-- url     : https://prove2.me/submissions/e7ab1258-70ba-4917-b260-2c9b07db0181

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd

set_option autoImplicit false

open Filter Topology

namespace Aux_CongestionApproxPNE_lemma_3
open CongestionApproxPNE

theorem ku_bound (L LL : ℝ) (k : ℕ) (hL : 0 < L) (hLL1 : 1 ≤ LL) (hLL : Real.exp LL = L)
    (h4 : 4 * LL ^ 2 ≤ L) (hk : (k : ℝ) < L / (2 * LL) + 1) :
    (k : ℝ) * Real.exp (L * (-(1 / (2 * ((k : ℝ) + 1))))) ≤
      Real.exp 1 / (2 * LL) + Real.exp 1 / L := by
  have hLL0 : 0 < LL := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 * ((k : ℝ) + 1) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = L / LL := ⟨_, rfl⟩
  have hqLL : q * LL = L := by rw [hq, div_mul_cancel₀ _ hLL0.ne']
  have e1 : L / LL / 2 = L / (2 * LL) := by rw [div_div, mul_comm LL 2]
  have ht2 : t < q + 4 := by
    have h1 : (k : ℝ) < q / 2 + 1 := by rw [hq, e1]; exact hk
    rw [ht]
    linarith
  have hq4 : 4 * LL ≤ q := by
    rw [hq, le_div_iff₀ hLL0]
    have : 4 * LL * LL = 4 * LL ^ 2 := by ring
    linarith
  -- step 1: the exponent is at most 1 - LL
  have hstep1 : L * (-(1 / t)) ≤ 1 - LL := by
    have h1 : (LL - 1) * t ≤ L := by
      have h2 : (LL - 1) * t ≤ (LL - 1) * (q + 4) :=
        mul_le_mul_of_nonneg_left ht2.le (by linarith)
      have h3 : (LL - 1) * (q + 4) = L - q + 4 * LL - 4 := by
        linear_combination hqLL
      linarith
    have h5 : LL - 1 ≤ L / t := by
      rw [le_div_iff₀ htpos]
      exact h1
    have h6 : L * (-(1 / t)) = -(L / t) := by ring
    rw [h6]
    linarith
  have hexp : Real.exp (L * (-(1 / t))) ≤ Real.exp 1 / L := by
    calc Real.exp (L * (-(1 / t))) ≤ Real.exp (1 - LL) := Real.exp_le_exp.mpr hstep1
      _ = Real.exp 1 / L := by rw [Real.exp_sub, hLL]
  rw [← ht]
  have hA : 0 ≤ L / (2 * LL) + 1 := by
    have : 0 ≤ L / (2 * LL) := div_nonneg hL.le (by linarith)
    linarith
  have hkb : (k : ℝ) * Real.exp (L * (-(1 / t))) ≤ (L / (2 * LL) + 1) * (Real.exp 1 / L) := by
    have hpos : 0 ≤ Real.exp (L * (-(1 / t))) := (Real.exp_pos _).le
    calc (k : ℝ) * Real.exp (L * (-(1 / t))) ≤ (L / (2 * LL) + 1) * Real.exp (L * (-(1 / t))) :=
          mul_le_mul_of_nonneg_right hk.le hpos
      _ ≤ (L / (2 * LL) + 1) * (Real.exp 1 / L) :=
          mul_le_mul_of_nonneg_left hexp hA
  have he : (L / (2 * LL) + 1) * (Real.exp 1 / L) = Real.exp 1 / (2 * LL) + Real.exp 1 / L := by
    rw [add_mul, one_mul, div_mul_div_comm, mul_comm L (Real.exp 1),
      mul_div_mul_right _ _ hL.ne']
  linarith

theorem g1_aux :
    Tendsto (fun d : ℕ => (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d)
      atTop (𝓝 1) := by
  have hL : Tendsto (fun d : ℕ => Real.log d) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL : Tendsto (fun d : ℕ => Real.log (Real.log d)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hsq := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hL
  have ev1 := hsq.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have ev2 := hLL.eventually_ge_atTop 1
  have ev3 := hL.eventually_ge_atTop 1
  have ev4 : ∀ᶠ d : ℕ in atTop, 1 ≤ d := Filter.eventually_ge_atTop 1
  have hg0 : Tendsto (fun d : ℕ => Real.exp 1 * (2 * Real.log (Real.log d))⁻¹ +
      Real.exp 1 * (Real.log d)⁻¹) atTop (𝓝 0) := by
    have h := ((Filter.Tendsto.const_mul_atTop two_pos hLL).inv_tendsto_atTop.const_mul
      (Real.exp 1)).add (hL.inv_tendsto_atTop.const_mul (Real.exp 1))
    simpa using h
  have hku : Tendsto (fun d : ℕ => (kd d : ℝ) *
      Real.exp (Real.log d * (-(1 / (2 * ((kd d : ℝ) + 1)))))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg0 ?_ ?_
    · exact Filter.Eventually.of_forall (fun d => mul_nonneg (Nat.cast_nonneg _)
        (Real.exp_pos _).le)
    · filter_upwards [ev1, ev2, ev3] with d h1 h2 h3
      have h1' : Real.log (Real.log d) ^ 2 / (1 * Real.log d + 0) < 1 / 4 := h1
      have h2' : 1 ≤ Real.log (Real.log d) := h2
      have h3' : 1 ≤ Real.log d := h3
      have hLpos : 0 < Real.log d := by linarith
      have h4 : 4 * Real.log (Real.log d) ^ 2 ≤ Real.log d := by
        rw [one_mul, add_zero, div_lt_iff₀ hLpos] at h1'
        linarith
      have hnn : 0 ≤ Real.log d / (2 * Real.log (Real.log d)) :=
        div_nonneg hLpos.le (by linarith)
      have hk : ((kd d : ℕ) : ℝ) < Real.log d / (2 * Real.log (Real.log d)) + 1 :=
        Nat.ceil_lt_add_one hnn
      have hb := ku_bound (Real.log d) (Real.log (Real.log d)) (kd d) hLpos h2'
        (Real.exp_log hLpos) h4 hk
      have e2 : Real.exp 1 / (2 * Real.log (Real.log d)) + Real.exp 1 / Real.log d =
          Real.exp 1 * (2 * Real.log (Real.log d))⁻¹ + Real.exp 1 * (Real.log d)⁻¹ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
      exact hb.trans e2.le
  have hexp := (Real.continuous_exp.tendsto 0).comp hku
  rw [Real.exp_zero] at hexp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · refine Filter.Eventually.of_forall (fun d => ?_)
    have hu : (0 : ℝ) ≤ (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1)))) :=
      Real.rpow_nonneg (Nat.cast_nonneg d) _
    exact one_le_pow₀ (show (1 : ℝ) ≤ 1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1)))) by linarith)
  · filter_upwards [ev4] with d hd
    have hdpos : (0 : ℝ) < d := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hu : (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1)))) =
        Real.exp (Real.log d * (-(1 / (2 * ((kd d : ℝ) + 1))))) := Real.rpow_def_of_pos hdpos _
    have hu0 : (0 : ℝ) ≤ (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1)))) :=
      Real.rpow_nonneg (Nat.cast_nonneg d) _
    show (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d ≤
      Real.exp ((kd d : ℝ) * Real.exp (Real.log d * (-(1 / (2 * ((kd d : ℝ) + 1))))))
    rw [← hu]
    calc (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d
        ≤ Real.exp ((d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d := by
          apply pow_le_pow_left₀ (by linarith)
          have := Real.add_one_le_exp ((d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1)))))
          linarith
      _ = Real.exp ((kd d : ℝ) * (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) :=
          (Real.exp_nat_mul _ _).symm

lemma key (d : ℕ) (hd : 2 ≤ d) :
    0 ≤ 2 * Real.sqrt (d : ℝ) / ((1 + Real.log (d : ℝ) / (2 * (d : ℝ))) ^ d * Real.log (d : ℝ)) ∧
    2 * Real.sqrt (d : ℝ) / ((1 + Real.log (d : ℝ) / (2 * (d : ℝ))) ^ d * Real.log (d : ℝ)) ≤
      2 * Real.exp 1 / Real.log (d : ℝ) := by
  have hD : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (d : ℝ) := ⟨_, rfl⟩
  rw [← hDdef] at hD ⊢
  have hDpos : 0 < D := by linarith
  have hx : 0 < Real.log D := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDpos.le
  have hlogs : Real.log (Real.sqrt D) = Real.log D / 2 := Real.log_sqrt hDpos.le
  have hxs : Real.log D ≤ 2 * Real.sqrt D := by
    have := Real.log_le_sub_one_of_pos hs
    linarith
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = Real.log D := ⟨_, rfl⟩
  rw [← hxdef] at hx hlogs hxs ⊢
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = x / (2 * D) := ⟨_, rfl⟩
  rw [← hydef]
  have hy : 0 ≤ y := by rw [hydef]; exact div_nonneg hx.le (by linarith)
  have hDy : D * y = x / 2 := by
    rw [hydef, mul_div_assoc', div_eq_div_iff (ne_of_gt (by linarith)) (by norm_num)]
    ring
  have hxy : x * y ≤ 2 := by
    have hxx : x * x ≤ 4 * D := by
      nlinarith [mul_le_mul hxs hxs hx.le (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt D)]
    rw [hydef, mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < 2 * D)]
    linarith
  have h1y : 0 < 1 + y := by linarith
  have hL : y ≤ (1 + y) * Real.log (1 + y) := by
    have h := Real.one_sub_inv_le_log_of_pos h1y
    have h2 := mul_le_mul_of_nonneg_left h h1y.le
    have h3 := mul_inv_cancel₀ h1y.ne'
    nlinarith
  have hkey : x / 2 - 1 ≤ D * Real.log (1 + y) := by
    have h2 : (x / 2 - 1) * (1 + y) ≤ (D * Real.log (1 + y)) * (1 + y) := by
      have h4 := mul_le_mul_of_nonneg_left hL hDpos.le
      nlinarith
    exact le_of_mul_le_mul_right h2 h1y
  have hP : (1 + y) ^ d = Real.exp (D * Real.log (1 + y)) := by
    rw [← Real.exp_log (pow_pos h1y d), Real.log_pow, hDdef]
  have hP0 : 0 < (1 + y) ^ d := pow_pos h1y d
  have hsqrt_le : Real.sqrt D ≤ Real.exp 1 * (1 + y) ^ d := by
    have e1 : Real.sqrt D = Real.exp (x / 2) := by rw [← hlogs, Real.exp_log hs]
    have e2 : Real.exp (x / 2) = Real.exp 1 * Real.exp (x / 2 - 1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e1, e2, hP]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) (Real.exp_pos 1).le
  constructor
  · exact div_nonneg (by positivity) (mul_nonneg hP0.le hx.le)
  · rw [div_le_div_iff₀ (mul_pos hP0 hx) hx]
    nlinarith [mul_le_mul_of_nonneg_right hsqrt_le hx.le]

theorem g2_aux :
    Tendsto (fun d : ℕ => 2 * Real.sqrt d / ((1 + Real.log d / (2 * d)) ^ d * Real.log d))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun d : ℕ => 2 * Real.exp 1 / Real.log (d : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with d hd using (key d hd).1
  · filter_upwards [eventually_ge_atTop 2] with d hd using (key d hd).2

end Aux_CongestionApproxPNE_lemma_3

open CongestionApproxPNE Aux_CongestionApproxPNE_lemma_3 in
theorem solution :
    Tendsto (fun d : ℕ => (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d +
        2 * Real.sqrt d / (Real.log d * (1 + Real.log d / (2 * d)) ^ d))
      atTop (𝓝 1) := by
  have h2 : Tendsto (fun d : ℕ => 2 * Real.sqrt d / (Real.log d * (1 + Real.log d / (2 * d)) ^ d))
      atTop (𝓝 0) := by
    refine g2_aux.congr (fun d => ?_)
    rw [mul_comm (Real.log (d : ℝ))]
  have h := g1_aux.add h2
  rw [add_zero] at h
  exact h
