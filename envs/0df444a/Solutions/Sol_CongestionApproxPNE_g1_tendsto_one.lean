-- Prove2me | solution 1 for CongestionApproxPNE.g1_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:31:49.541769+00:00
-- url     : https://prove2.me/submissions/e9ff159a-b20d-477e-96f3-a4e013ef641c

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd

set_option autoImplicit false

open Filter Topology

namespace Aux_CongestionApproxPNE_g1_tendsto_one
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

end Aux_CongestionApproxPNE_g1_tendsto_one

open CongestionApproxPNE Aux_CongestionApproxPNE_g1_tendsto_one in
theorem solution :
    Tendsto (fun d : ℕ => (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d)
      atTop (𝓝 1) :=
  g1_aux

