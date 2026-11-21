-- Prove2me | solution 1 for CongestionApproxPNE.ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:55:54.680547+00:00
-- url     : https://prove2.me/submissions/5d70e2d4-78cc-49a8-9343-e18d58c4a0c4

import Mathlib
import Definitions.Def_CongestionApproxPNE_ratioOne
import Definitions.Def_CongestionApproxPNE_ratioTwo
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

namespace Aux_CongestionApproxPNE_ratio_bounds
open CongestionApproxPNE Filter Topology

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

theorem log_four_gt : 1 < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 : (2.7182818286 : ℝ) < 4 := by norm_num
  exact lt_trans h1 h2

theorem facts (d : ℕ) (hd : 4 ≤ d) :
    0 < (d : ℝ) ∧ 1 < Real.log d ∧ 0 < Real.log (Real.log d) ∧
    (d : ℝ) ^ (1 / (2 * ((kd d : ℝ) + 1))) ≤ Real.log d ∧
    (d : ℝ) ^ (1 / (2 * ((kd d : ℝ) + 1))) * (d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) =
      √(d : ℝ) ∧
    ((d : ℝ) ^ (1 / (2 * ((kd d : ℝ) + 1)))) ^ (kd d) =
      (d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) := by
  have hD4 : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : (0 : ℝ) < d := by linarith
  have hL : 1 < Real.log d := lt_of_lt_of_le log_four_gt (Real.log_le_log (by norm_num) hD4)
  have hLL : 0 < Real.log (Real.log d) := Real.log_pos hL
  have hk0 : (0 : ℝ) ≤ kd d := Nat.cast_nonneg _
  have hk1 : (0 : ℝ) < 2 * ((kd d : ℝ) + 1) := by linarith
  refine ⟨hD, hL, hLL, ?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hD]
    have hkc : Real.log d / (2 * Real.log (Real.log d)) ≤ (kd d : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ (show (0 : ℝ) < 2 * Real.log (Real.log d) by linarith)] at hkc
    have e1 : (kd d : ℝ) * (2 * Real.log (Real.log d)) = 2 * (kd d : ℝ) * Real.log (Real.log d) := by
      ring
    have h2 : Real.log d * (1 / (2 * ((kd d : ℝ) + 1))) ≤ Real.log (Real.log d) := by
      rw [mul_one_div, div_le_iff₀ hk1]
      have e2 : Real.log (Real.log d) * (2 * ((kd d : ℝ) + 1)) =
          2 * (kd d : ℝ) * Real.log (Real.log d) + 2 * Real.log (Real.log d) := by ring
      linarith
    calc Real.exp (Real.log d * (1 / (2 * ((kd d : ℝ) + 1))))
        ≤ Real.exp (Real.log (Real.log d)) := Real.exp_le_exp.mpr h2
      _ = Real.log d := Real.exp_log (by linarith)
  · rw [← Real.rpow_add hD, Real.sqrt_eq_rpow]
    congr 1
    rw [← add_div, div_eq_iff hk1.ne']
    ring
  · rw [← Real.rpow_mul_natCast hD.le]
    congr 1
    rw [div_mul_eq_mul_div, one_mul]

theorem part2 (d : ℕ) (hd : 4 ≤ d) :
    √(d : ℝ) / (2 * Real.log d) ≤ ratioTwo d (nChoice d) (kd d) (wChoice d) (betaChoice d) := by
  obtain ⟨hD, hL, hLL, hDa, hac, hpk⟩ := facts d hd
  obtain ⟨A, hA⟩ : ∃ A, A = (d : ℝ) ^ (1 / (2 * ((kd d : ℝ) + 1))) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = (d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) := ⟨_, rfl⟩
  rw [← hA] at hDa hac hpk
  rw [← hC] at hac hpk
  have hApos : 0 < A := by rw [hA]; exact Real.rpow_pos_of_pos hD _
  have hCpos : 0 < C := by rw [hC]; exact Real.rpow_pos_of_pos hD _
  obtain ⟨w, hw⟩ : ∃ w, w = wChoice d := ⟨_, rfl⟩
  have hwpos : 0 < w := by
    rw [hw]
    unfold wChoice
    exact div_pos (by linarith) (by linarith)
  have hP : 0 < (1 + w) ^ d := pow_pos (by linarith) d
  have hβ : betaChoice d = 1 / (C * (1 + w) ^ d) := by
    unfold betaChoice
    rw [← hC, ← hw]
  have hn : (nChoice d : ℝ) ≤ 1 / (A * w) := by
    unfold nChoice
    rw [← hA, ← hw]
    exact Nat.floor_le (le_of_lt (one_div_pos.mpr (mul_pos hApos hwpos)))
  unfold ratioTwo
  rw [hβ, ← hw]
  have hn0 : (0 : ℝ) ≤ nChoice d := Nat.cast_nonneg _
  have hnw : (nChoice d : ℝ) * w ≤ 1 / A := by
    have h1 := mul_le_mul_of_nonneg_right hn hwpos.le
    have e : 1 / (A * w) * w = 1 / A := by
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hwpos.ne']
    linarith
  have hnwk : ((nChoice d : ℝ) * w) ^ kd d ≤ 1 / C := by
    have h1 := pow_le_pow_left₀ (mul_nonneg hn0 hwpos.le) hnw (kd d)
    rw [one_div_pow, hpk] at h1
    exact h1
  have hβP : 1 / (C * (1 + w) ^ d) * (1 + w) ^ d = 1 / C := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hP.ne']
  have hβ0 : 0 ≤ 1 / (C * (1 + w) ^ d) := le_of_lt (one_div_pos.mpr (mul_pos hCpos hP))
  have hden0 : 0 < ((nChoice d : ℝ) * w) ^ kd d + 1 / (C * (1 + w) ^ d) * (1 + w) ^ d := by
    rw [hβP]
    have := pow_nonneg (mul_nonneg hn0 hwpos.le) (kd d)
    have := one_div_pos.mpr hCpos
    linarith
  have hden : ((nChoice d : ℝ) * w) ^ kd d + 1 / (C * (1 + w) ^ d) * (1 + w) ^ d ≤ 2 / C := by
    rw [hβP]
    have e : 1 / C + 1 / C = 2 / C := by ring
    linarith
  have hnum : 1 ≤ (1 + w) ^ kd d + 1 / (C * (1 + w) ^ d) * w ^ d := by
    have h1 : 1 ≤ (1 + w) ^ kd d := one_le_pow₀ (by linarith)
    have h2 : 0 ≤ 1 / (C * (1 + w) ^ d) * w ^ d := mul_nonneg hβ0 (pow_nonneg hwpos.le d)
    linarith
  have hr1 : 1 / (((nChoice d : ℝ) * w) ^ kd d + 1 / (C * (1 + w) ^ d) * (1 + w) ^ d) ≤
      ((1 + w) ^ kd d + 1 / (C * (1 + w) ^ d) * w ^ d) /
        (((nChoice d : ℝ) * w) ^ kd d + 1 / (C * (1 + w) ^ d) * (1 + w) ^ d) :=
    div_le_div_of_nonneg_right hnum hden0.le
  have hr2 : 1 / (2 / C) ≤
      1 / (((nChoice d : ℝ) * w) ^ kd d + 1 / (C * (1 + w) ^ d) * (1 + w) ^ d) :=
    one_div_le_one_div_of_le hden0 hden
  have hr3 : 1 / (2 / C) = C / 2 := one_div_div 2 C
  have hgoal : √(d : ℝ) / (2 * Real.log d) ≤ C / 2 := by
    rw [div_le_iff₀ (show (0 : ℝ) < 2 * Real.log d by linarith)]
    have h1 : A * C ≤ Real.log d * C := mul_le_mul_of_nonneg_right hDa hCpos.le
    have e : C / 2 * (2 * Real.log d) = Real.log d * C := by ring
    linarith
  linarith

theorem part1_at (d : ℕ) (hd : 4 ≤ d)
    (hg1 : (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d < 3 / 2)
    (hLe : 4 * Real.exp 1 ≤ Real.log d) :
    √(d : ℝ) / (2 * Real.log d) ≤ ratioOne d (nChoice d) (kd d) (wChoice d) (betaChoice d) := by
  obtain ⟨hD, hL, hLL, hDa, hac, hpk⟩ := facts d hd
  have hkey := (key d (by omega)).2
  obtain ⟨A, hA⟩ : ∃ A, A = (d : ℝ) ^ (1 / (2 * ((kd d : ℝ) + 1))) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = (d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) := ⟨_, rfl⟩
  rw [← hA] at hDa hac hpk
  rw [← hC] at hac hpk
  have hApos : 0 < A := by rw [hA]; exact Real.rpow_pos_of_pos hD _
  have hCpos : 0 < C := by rw [hC]; exact Real.rpow_pos_of_pos hD _
  have hD1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hC1 : 1 ≤ C := by
    rw [hC]
    apply Real.one_le_rpow hD1
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hneg : (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1)))) = 1 / A := by
    rw [Real.rpow_neg hD.le, ← hA, one_div]
  rw [hneg] at hg1
  obtain ⟨S, hS⟩ : ∃ S, S = √(d : ℝ) := ⟨_, rfl⟩
  rw [← hS] at hac hkey ⊢
  have hSpos : 0 < S := by rw [hS]; exact Real.sqrt_pos.mpr hD
  have hS2 : S ^ 2 = (d : ℝ) := by rw [hS]; exact Real.sq_sqrt hD.le
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (d : ℝ) := ⟨_, rfl⟩
  rw [← hLdef] at hL hDa hLe hkey ⊢
  have hLpos : 0 < L := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = wChoice d := ⟨_, rfl⟩
  have hw' : wChoice d = Real.log (d : ℝ) / (2 * (d : ℝ)) := rfl
  have hwS : w = L / (2 * S ^ 2) := by
    rw [hw, hw', ← hLdef, ← hS2]
  have hwpos : 0 < w := by rw [hwS]; exact div_pos hLpos (mul_pos two_pos (pow_pos hSpos 2))
  obtain ⟨P, hPdef⟩ : ∃ P, P = (1 + w) ^ d := ⟨_, rfl⟩
  have hP : 0 < P := by rw [hPdef]; exact pow_pos (by linarith) d
  -- the bound (1+w)^d ≥ S/e from the g₂ estimate
  have hSP : S ≤ Real.exp 1 * P := by
    have hk2 : 2 * S / (P * L) ≤ 2 * Real.exp 1 / L := by
      rw [hPdef, hw, hw', ← hLdef]
      exact hkey
    rw [div_le_div_iff₀ (mul_pos hP hLpos) hLpos] at hk2
    have e : 2 * Real.exp 1 * (P * L) = (2 * (Real.exp 1 * P)) * L := by ring
    rw [e] at hk2
    have := le_of_mul_le_mul_right hk2 hLpos
    linarith
  have hβ : betaChoice d = 1 / (C * P) := by
    unfold betaChoice
    rw [← hC, ← hw, ← hPdef]
  obtain ⟨T, hT⟩ : ∃ T, T = 1 / (A * w) := ⟨_, rfl⟩
  have hTpos : 0 < T := by rw [hT]; exact one_div_pos.mpr (mul_pos hApos hwpos)
  have hn1 : (nChoice d : ℝ) ≤ T := by
    unfold nChoice
    rw [← hA, ← hw, ← hT]
    exact Nat.floor_le hTpos.le
  have hn2 : T - 1 ≤ (nChoice d : ℝ) := by
    have : T < (nChoice d : ℝ) + 1 := by
      unfold nChoice
      rw [← hA, ← hw, ← hT]
      exact Nat.lt_floor_add_one T
    linarith
  have hn0 : (0 : ℝ) ≤ nChoice d := Nat.cast_nonneg _
  -- T / C = 2 S / L
  have hTC : T / C = 2 * S / L := by
    have e1 : A * w * C = L / (2 * S) := by
      rw [mul_right_comm, hac, hwS, mul_div_assoc',
        div_eq_div_iff (mul_ne_zero two_ne_zero (pow_ne_zero 2 hSpos.ne'))
          (mul_ne_zero two_ne_zero hSpos.ne')]
      ring
    rw [hT, div_div, e1, one_div_div]
  have hTw : T * w = 1 / A := by
    rw [hT, div_mul_eq_mul_div, mul_div_mul_right _ _ hwpos.ne']
  unfold ratioOne
  rw [hβ, ← hw, ← hPdef]
  -- numerator
  have hnum : 2 * S / L ≤ 1 + (nChoice d : ℝ) * (1 / (C * P)) * P := by
    have e1 : (nChoice d : ℝ) * (1 / (C * P)) * P = (nChoice d : ℝ) / C := by
      rw [mul_assoc, div_mul_eq_mul_div, mul_div_mul_right _ _ hP.ne', mul_one_div]
    rw [e1]
    have h1 : (T - 1) / C ≤ (nChoice d : ℝ) / C := div_le_div_of_nonneg_right hn2 hCpos.le
    have h2 : (T - 1) / C = T / C - 1 / C := sub_div T 1 C
    have h3 : 1 / C ≤ 1 := by rw [div_le_one hCpos]; exact hC1
    linarith
  -- denominator
  have hden1 : (1 + (nChoice d : ℝ) * w) ^ kd d ≤ (1 + 1 / A) ^ kd d := by
    apply pow_le_pow_left₀ (by have := mul_nonneg hn0 hwpos.le; linarith)
    have := mul_le_mul_of_nonneg_right hn1 hwpos.le
    linarith
  have hden2 : (nChoice d : ℝ) * (1 / (C * P)) ≤ 1 / 2 := by
    have h1 : (nChoice d : ℝ) * (1 / (C * P)) ≤ T * (1 / (C * P)) :=
      mul_le_mul_of_nonneg_right hn1 (le_of_lt (one_div_pos.mpr (mul_pos hCpos hP)))
    have e2 : T * (1 / (C * P)) = T / C / P := by
      rw [mul_one_div, div_div]
    have h2 : T / C / P = 2 * S / L / P := by rw [hTC]
    have h3 : 2 * S / L / P ≤ 1 / 2 := by
      rw [div_div, div_le_iff₀ (mul_pos hLpos hP)]
      nlinarith [hSP, mul_le_mul_of_nonneg_right hLe hP.le]
    linarith
  have hden0 : 0 < (1 + (nChoice d : ℝ) * w) ^ kd d + (nChoice d : ℝ) * (1 / (C * P)) := by
    have h1 : 1 ≤ (1 + (nChoice d : ℝ) * w) ^ kd d := one_le_pow₀ (by
      have := mul_nonneg hn0 hwpos.le
      linarith)
    have h2 : 0 ≤ (nChoice d : ℝ) * (1 / (C * P)) :=
      mul_nonneg hn0 (le_of_lt (one_div_pos.mpr (mul_pos hCpos hP)))
    linarith
  have hden : (1 + (nChoice d : ℝ) * w) ^ kd d + (nChoice d : ℝ) * (1 / (C * P)) ≤ 2 := by
    linarith
  have hr : (1 + (nChoice d : ℝ) * (1 / (C * P)) * P) / 2 ≤
      (1 + (nChoice d : ℝ) * (1 / (C * P)) * P) /
        ((1 + (nChoice d : ℝ) * w) ^ kd d + (nChoice d : ℝ) * (1 / (C * P))) := by
    apply div_le_div_of_nonneg_left _ hden0 hden
    have := div_pos (mul_pos two_pos hSpos) hLpos
    linarith
  have hfin : S / (2 * L) ≤ (1 + (nChoice d : ℝ) * (1 / (C * P)) * P) / 2 := by
    have e3 : S / (2 * L) = (2 * S / L) / 4 := by
      rw [div_div, div_eq_div_iff (mul_ne_zero two_ne_zero hLpos.ne')
        (mul_ne_zero hLpos.ne' (by norm_num))]
      ring
    have h4 : 0 ≤ 2 * S / L := le_of_lt (div_pos (mul_pos two_pos hSpos) hLpos)
    rw [e3]
    linarith
  linarith

end Aux_CongestionApproxPNE_ratio_bounds

open CongestionApproxPNE Aux_CongestionApproxPNE_ratio_bounds in
theorem solution :
    (∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Real.sqrt d / (2 * Real.log d) ≤
        ratioOne d (nChoice d) (kd d) (wChoice d) (betaChoice d)) ∧
    (∀ d : ℕ, 4 ≤ d →
      Real.sqrt d / (2 * Real.log d) ≤
        ratioTwo d (nChoice d) (kd d) (wChoice d) (betaChoice d)) := by
  refine ⟨?_, fun d hd => part2 d hd⟩
  have hL : Filter.Tendsto (fun d : ℕ => Real.log d) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ev1 := g1_aux.eventually (gt_mem_nhds (show (1 : ℝ) < 3 / 2 by norm_num))
  have ev2 := hL.eventually_ge_atTop (4 * Real.exp 1)
  have ev3 : ∀ᶠ d : ℕ in Filter.atTop, 4 ≤ d := Filter.eventually_ge_atTop 4
  obtain ⟨d₀, hd₀⟩ := Filter.eventually_atTop.mp (ev1.and (ev2.and ev3))
  exact ⟨d₀, fun d hd => part1_at d (hd₀ d hd).2.2 (hd₀ d hd).1 (hd₀ d hd).2.1⟩
