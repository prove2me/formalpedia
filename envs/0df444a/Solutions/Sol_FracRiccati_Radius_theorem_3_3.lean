-- Prove2me | solution 1 for FracRiccati.Radius.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:57:44.636226+00:00
-- url     : https://prove2.me/submissions/843ade49-2bc1-4ab7-a27f-f5c1b0913396

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff
import Definitions.Def_FracRiccati_Radius_Constants
import Theorems.Thm_FracRiccati_Radius_coeff_bound_B_49
import Theorems.Thm_FracRiccati_Radius_coeff_bound_B_51
import Theorems.Thm_FracRiccati_Radius_prop_B_1_b
import Theorems.Thm_FracRiccati_Radius_theorem_3_3_c
import Theorems.Thm_FracRiccati_Radius_lower_propagation_B_1_2
import Theorems.Thm_FracRiccati_Radius_lower_propagation_B_2_2
import Theorems.Thm_FracRiccati_Radius_riemann_sum_B_52
open Filter Topology

namespace Aux_FRR_T33
open FracRiccati.Radius

lemma enn_bridge (x : ℂ) (hx : x ≠ 0) (e : ℝ) :
    ((‖x‖₊ : ENNReal) ^ e) = ENNReal.ofReal (‖x‖ ^ e) := by
  rw [← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hx)]
  congr 1
  simp [ENNReal.ofReal, Real.toNNReal_of_nonneg (norm_nonneg x)]
  rfl

lemma enn_zero (e : ℝ) (he : e < 0) : ((‖(0:ℂ)‖₊ : ENNReal) ^ e) = ⊤ := by
  simp [ENNReal.zero_rpow_of_neg he]

lemma tend_lower (α C ρ : ℝ) (hα : 0 < α) (hC : 0 < C) (hρ : 0 < ρ) :
    Tendsto (fun k : ℕ => (C * (k:ℝ) ^ (α - 1) * ρ ^ k) ^ (-(1 / (α * k)))) atTop
      (𝓝 (ρ ^ (-(1 / α)))) := by
  have h1 : Tendsto (fun k : ℕ => (1:ℝ) / k) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun k : ℕ => Real.log k / k) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    refine this.congr' (Eventually.of_forall fun k => ?_)
    simp
  have hin : Tendsto (fun k : ℕ => Real.exp (-(1/α) * (Real.log C * ((1:ℝ)/k) +
      (α - 1) * (Real.log k / k) + Real.log ρ))) atTop (𝓝 (ρ ^ (-(1 / α)))) := by
    rw [Real.rpow_def_of_pos hρ]
    apply (Real.continuous_exp.tendsto _).comp
    have := ((h1.const_mul (Real.log C)).add (h2.const_mul (α - 1))).add_const (Real.log ρ)
    have := this.const_mul (-(1/α))
    convert this using 2
    ring
  refine hin.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hg : 0 < C * (k:ℝ) ^ (α - 1) * ρ ^ k := by positivity
  rw [Real.rpow_def_of_pos hg, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hk', Real.log_pow]
  congr 1
  field_simp

lemma radius_lower (α C ρ : ℝ) (hα : 0 < α) (hC : 0 < C) (hρ : 0 < ρ) (a : ℕ → ℂ)
    (h : ∀ k : ℕ, 1 ≤ k → ‖a k‖ ≤ C * (k:ℝ) ^ (α - 1) * ρ ^ k) :
    ENNReal.ofReal (ρ ^ (-(1 / α))) ≤ radius α a := by
  unfold radius
  apply le_of_forall_lt_imp_le_of_dense
  intro b hb
  have hbt : b ≠ ⊤ := ne_top_of_lt hb
  have hbr : b.toReal < ρ ^ (-(1 / α)) := ENNReal.toReal_lt_of_lt_ofReal hb
  have hev := (tend_lower α C ρ hα hC hρ).eventually (lt_mem_nhds hbr)
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
  have hk' : (0:ℝ) < k := by exact_mod_cast hk1
  have he : -(1 / (α * k)) < 0 := by
    have : 0 < 1 / (α * k) := by positivity
    linarith
  by_cases h0 : a k = 0
  · rw [h0, enn_zero _ he]; exact le_top
  · rw [enn_bridge _ h0, ← ENNReal.ofReal_toReal hbt]
    apply ENNReal.ofReal_le_ofReal
    refine hk.le.trans ?_
    exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr h0) (h k hk1) he.le

lemma tend_upper (α c ρ : ℝ) (hα : 0 < α) (hc : 0 < c) (hρ : 0 < ρ) :
    Tendsto (fun k : ℕ => (c * ρ ^ k * (k:ℝ) ^ (α - 1)) ^ (-(1 / (α * (2 * (k:ℝ) - 1))))) atTop
      (𝓝 (ρ ^ (-(1 / (2 * α))))) := by
  have h1 : Tendsto (fun k : ℕ => (1:ℝ) / (2 * (k:ℝ) - 1)) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 2 (-1) 0 two_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    refine this.congr' (Eventually.of_forall fun k => ?_)
    simp [sub_eq_add_neg]
  have h2 : Tendsto (fun k : ℕ => Real.log k / (2 * (k:ℝ) - 1)) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 2 (-1) 1 two_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    refine this.congr' (Eventually.of_forall fun k => ?_)
    simp [sub_eq_add_neg]
  have hin : Tendsto (fun k : ℕ => Real.exp (-(1/α) * (Real.log c * ((1:ℝ) / (2 * (k:ℝ) - 1)) +
      Real.log ρ * (1/2 + ((1:ℝ) / (2 * (k:ℝ) - 1)) / 2) +
      (α - 1) * (Real.log k / (2 * (k:ℝ) - 1))))) atTop (𝓝 (ρ ^ (-(1 / (2 * α))))) := by
    rw [Real.rpow_def_of_pos hρ]
    apply (Real.continuous_exp.tendsto _).comp
    have := (((h1.const_mul (Real.log c)).add
      (((h1.div_const 2).const_add (1/2)).const_mul (Real.log ρ))).add
      (h2.const_mul (α - 1))).const_mul (-(1/α))
    convert this using 2
    field_simp
    ring
  refine hin.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hk2 : (0:ℝ) < 2 * k - 1 := by linarith
  have hg : 0 < c * ρ ^ k * (k:ℝ) ^ (α - 1) := by positivity
  rw [Real.rpow_def_of_pos hg, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hk0, Real.log_pow]
  congr 1
  field_simp
  ring

lemma radius_upper (α c ρ : ℝ) (hα : 0 < α) (hc : 0 < c) (hρ : 0 < ρ) (a : ℕ → ℂ)
    (h : ∀ k : ℕ, 1 ≤ k → c * ρ ^ k * (k:ℝ) ^ (α - 1) ≤ ‖a (2 * k - 1)‖) :
    radius α a ≤ ENNReal.ofReal (ρ ^ (-(1 / (2 * α)))) := by
  unfold radius
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  by_cases hbt : b = ⊤
  · rw [hbt]; exact le_top
  have hbr : ρ ^ (-(1 / (2 * α))) < b.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hbt).mp hb
  have hev := (tend_upper α c ρ hα hc hρ).eventually (gt_mem_nhds hbr)
  apply Filter.liminf_le_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  set k := max K (N + 1) with hkdef
  have hk1 : 1 ≤ k := by omega
  refine ⟨2 * k - 1, by omega, ?_⟩
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hg : 0 < c * ρ ^ k * (k:ℝ) ^ (α - 1) := by positivity
  have hle := h k hk1
  have hak : a (2 * k - 1) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hle; linarith
  have hcast : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have he : -(1 / (α * (2 * (k:ℝ) - 1))) ≤ 0 := by
    have : 0 < 1 / (α * (2 * (k:ℝ) - 1)) := by
      have : (0:ℝ) < 2 * k - 1 := by linarith
      positivity
    linarith
  rw [enn_bridge _ hak, ← ENNReal.ofReal_toReal hbt, hcast]
  apply ENNReal.ofReal_le_ofReal
  calc ‖a (2 * k - 1)‖ ^ (-(1 / (α * (2 * (k:ℝ) - 1))))
      ≤ (c * ρ ^ k * (k:ℝ) ^ (α - 1)) ^ (-(1 / (α * (2 * (k:ℝ) - 1)))) :=
        Real.rpow_le_rpow_of_nonpos hg hle he
    _ ≤ b.toReal := (hK k (le_max_left _ _)).le

lemma coeff_rec (α : ℝ) (lam mu nu : ℂ) (j : ℕ) : coeff α lam mu nu (j + 2) =
    (lam * ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ)
      + mu * coeff α lam mu nu (j + 1)) *
      ((Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + 1) /
          Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + α + 1) : ℝ) : ℂ) := by
  rw [coeff, Finset.sum_attach (Finset.Ico 1 (j + 1))
    (fun ℓ => coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ))]

lemma coeff_neg (α : ℝ) (lam mu nu : ℂ) (k : ℕ) :
    coeff α (-lam) mu (-nu) k = -coeff α lam mu nu k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [coeff]
    | 1, _ => simp [coeff, neg_div]
    | j + 2, ih =>
      rw [coeff_rec, coeff_rec, ih (j + 1) (by omega)]
      have : ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α (-lam) mu (-nu) ℓ * coeff α (-lam) mu (-nu) (j + 1 - ℓ)
          = ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ) := by
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        rw [Finset.mem_Ico] at hℓ
        rw [ih ℓ (by omega), ih (j + 1 - ℓ) (by omega)]
        ring
      rw [this]
      ring

lemma radius_neg (α : ℝ) (a : ℕ → ℂ) : radius α (fun k => -a k) = radius α a := by
  unfold radius
  simp only [nnnorm_neg]

lemma rpow_aux (α N D : ℝ) (hα : 0 < α) (hN : 0 < N) (hD : 0 < D) :
    (N / D) ^ (-(1 / α)) = D ^ (1 / α) / N ^ (1 / α) := by
  rw [Real.rpow_neg (by positivity), Real.div_rpow hN.le hD.le, inv_div]

lemma exp_aux (α : ℝ) (hα : 0 < α) :
    (1 - max (1 - 2 * α) 0) * (1 / α) = 1 / α - max (1 / α - 2) 0 := by
  rcases le_or_gt α (1/2) with h | h
  · have h1 : max (1 - 2 * α) 0 = 1 - 2 * α := max_eq_left (by linarith)
    have h2 : 2 ≤ 1 / α := by rw [le_div_iff₀ hα]; linarith
    have h3 : max (1 / α - 2) 0 = 1 / α - 2 := max_eq_left (by linarith)
    rw [h1, h3]; field_simp
  · have h1 : max (1 - 2 * α) 0 = 0 := max_eq_right (by linarith)
    have h2 : 1 / α < 2 := by rw [div_lt_iff₀ hα]; linarith
    have h3 : max (1 / α - 2) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h3]; ring

lemma tau_eq_le1 (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (lam mu nu : ℂ) (hlam : lam ≠ 0)
    (hnu : nu ≠ 0) :
    tauStar α lam mu nu =
      ((‖mu‖ + Real.sqrt (‖mu‖ ^ 2 + (2 : ℝ) ^ (2 - max (1 - 2 * α) 0) *
        (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * ‖lam‖ * ‖nu‖)) /
        ((2 : ℝ) ^ (1 - max (1 - 2 * α) 0) * α ^ α)) ^ (-(1 / α)) := by
  have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα0
  have hmin : min α 1 = α := min_eq_left hα1
  have hmax : max (α - 1) 0 = 0 := max_eq_right (by linarith)
  have hsq : ‖mu‖ ^ 2 + cAlpha α * ‖lam‖ * ‖nu‖ / Real.Gamma α =
      ‖mu‖ ^ 2 + (2 : ℝ) ^ (2 - max (1 - 2 * α) 0) *
        (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * ‖lam‖ * ‖nu‖ := by
    unfold cAlpha betaFn
    rw [hmin, hmax, show α + α = 2 * α by ring]
    field_simp
    ring_nf
  have hpos : 0 < ‖lam‖ * ‖nu‖ := by positivity
  have hG2 : 0 < Real.Gamma (2 * α) := Real.Gamma_pos_of_pos (by linarith)
  have hN : 0 < ‖mu‖ + Real.sqrt (‖mu‖ ^ 2 + (2 : ℝ) ^ (2 - max (1 - 2 * α) 0) *
        (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * ‖lam‖ * ‖nu‖) := by
    have : 0 < Real.sqrt (‖mu‖ ^ 2 + (2 : ℝ) ^ (2 - max (1 - 2 * α) 0) *
        (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * ‖lam‖ * ‖nu‖) := by
      apply Real.sqrt_pos.mpr
      have : 0 < (2 : ℝ) ^ (2 - max (1 - 2 * α) 0) *
        (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * ‖lam‖ * ‖nu‖ := by positivity
      positivity
    positivity
  rw [rpow_aux α _ _ hα0 hN (by positivity)]
  unfold tauStar
  rw [hsq, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul hα0.le, exp_aux α hα0, mul_one_div_cancel hα0.ne', Real.rpow_one]

lemma tau_eq_gt1 (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (lam mu nu : ℂ) (hlam : lam ≠ 0)
    (hnu : nu ≠ 0) :
    tauStar α lam mu nu =
      ((‖mu‖ + Real.sqrt (‖mu‖ ^ 2 +
        (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) * ‖lam‖ * ‖nu‖ / Real.Gamma α)) / (2 * α ^ α))
        ^ (-(1 / α)) := by
  have hα0 : 0 < α := by linarith
  have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα0
  have hmin : min α 1 = 1 := min_eq_right hα1.le
  have hmax : max (α - 1) 0 = α - 1 := max_eq_left (by linarith)
  have hmax2 : max (1 - 2 * α) 0 = 0 := max_eq_right (by linarith)
  have hmax3 : max (1 / α - 2) 0 = 0 := by
    apply max_eq_right
    have : 1 / α < 1 := by rw [div_lt_one hα0]; exact hα1
    linarith
  have hsq : cAlpha α = (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) := by
    unfold cAlpha betaFn
    rw [hmin, hmax, hmax2]
    norm_num
    left; ring_nf
  have hpos : 0 < ‖lam‖ * ‖nu‖ := by positivity
  have hN : 0 < ‖mu‖ + Real.sqrt (‖mu‖ ^ 2 +
        (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) * ‖lam‖ * ‖nu‖ / Real.Gamma α) := by
    have : 0 < Real.sqrt (‖mu‖ ^ 2 +
        (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) * ‖lam‖ * ‖nu‖ / Real.Gamma α) := by
      apply Real.sqrt_pos.mpr
      have : 0 < (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) * ‖lam‖ * ‖nu‖ / Real.Gamma α := by
        positivity
      positivity
    positivity
  rw [rpow_aux α _ _ hα0 hN (by positivity)]
  unfold tauStar
  rw [hsq, hmax3, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hα0.le, mul_one_div_cancel hα0.ne', Real.rpow_one, sub_zero]

lemma eq_of_log_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : Real.log x = Real.log y) : x = y :=
  Real.log_injOn_pos (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) h

lemma upper_const_le1 (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (P : ℝ) (hP : 0 < P) :
    ((5 : ℝ) ^ (1 - α) / 3 * α ^ (-α) * P / Real.Gamma (α + 1)) ^ (-(1 / (2 * α))) =
      CAlpha α * (Real.Gamma (α + 1) / P) ^ (1 / (2 * α)) := by
  have hG : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  unfold CAlpha
  rw [if_pos hα1, Real.sqrt_eq_rpow]
  apply eq_of_log_eq (by positivity) (by positivity)
  have h5a : (0:ℝ) < (5 : ℝ) ^ (1 - α) := by positivity
  have h5b : (0:ℝ) < (5 : ℝ) ^ (α - 1) := by positivity
  have haa : (0:ℝ) < α ^ (-α) := by positivity
  rw [Real.log_rpow (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow hα0, Real.log_rpow (by positivity), Real.log_div (by positivity) hP.ne',
    Real.log_div (by positivity) hG.ne', Real.log_mul (by positivity) hP.ne',
    Real.log_mul (by positivity) haa.ne', Real.log_div h5a.ne' (by norm_num),
    Real.log_mul (by norm_num) h5b.ne']
  rw [Real.log_rpow (by norm_num : (0:ℝ) < 5) (α - 1)]
  try rw [Real.log_rpow (by norm_num : (0:ℝ) < 5) (1 - α)]
  try rw [Real.log_rpow hα0 (-α)]
  field_simp
  ring

lemma upper_const_gt1 (α : ℝ) (hα1 : 1 < α) (P B : ℝ) (hP : 0 < P) (hB : 0 < B) (hB1 : B ≤ 1) :
    (P * (2 * α) ^ (-α) * B / Real.Gamma (α + 1)) ^ (-(1 / (2 * α))) ≤
      Real.sqrt (2 * α) / B * (Real.Gamma (α + 1) / P) ^ (1 / (2 * α)) := by
  have hα0 : 0 < α := by linarith
  have hG : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h2a : (0:ℝ) < 2 * α := by linarith
  have heq : (P * (2 * α) ^ (-α) * B / Real.Gamma (α + 1)) ^ (-(1 / (2 * α))) =
      Real.sqrt (2 * α) * B ^ (-(1 / (2 * α))) * (Real.Gamma (α + 1) / P) ^ (1 / (2 * α)) := by
    rw [Real.sqrt_eq_rpow]
    apply eq_of_log_eq (by positivity) (by positivity)
    have haa : (0:ℝ) < (2 * α) ^ (-α) := by positivity
    rw [Real.log_rpow (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow h2a, Real.log_rpow hB,
      Real.log_rpow (by positivity), Real.log_div (by positivity) hP.ne',
      Real.log_div (by positivity) hG.ne', Real.log_mul (by positivity) hB.ne',
      Real.log_mul hP.ne' haa.ne', Real.log_rpow h2a]
    field_simp
    ring
  rw [heq, div_eq_mul_inv (Real.sqrt (2 * α))]
  have hBle : B ^ (-(1 / (2 * α))) ≤ B⁻¹ := by
    rw [← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_ge hB hB1
    have : 1 / (2 * α) ≤ 1 := by rw [div_le_one h2a]; linarith
    linarith
  have : 0 ≤ (Real.Gamma (α + 1) / P) ^ (1 / (2 * α)) := by positivity
  gcongr

end Aux_FRR_T33

open FracRiccati.Radius Aux_FRR_T33 in
theorem solution (α : ℝ) (hα0 : 0 < α) (hα2 : α ≤ 2) :
    (∀ lam mu nu : ℂ, lam ≠ 0 → nu ≠ 0 →
        0 < tauStar α lam mu nu ∧
        ENNReal.ofReal (tauStar α lam mu nu) ≤ radius α (coeff α lam mu nu)) ∧
    (∀ l m n : ℝ, ((0 < l ∧ 0 < n ∧ 0 ≤ m) ∨ (l < 0 ∧ n < 0 ∧ m ≤ 0)) →
        radius α (coeff α l m n) ≤ radius α (coeff α ((|l| : ℝ) : ℂ) 0 ((|n| : ℝ) : ℂ)) ∧
        radius α (coeff α ((|l| : ℝ) : ℂ) 0 ((|n| : ℝ) : ℂ)) ≤
          ENNReal.ofReal (CAlpha α * (Real.Gamma (α + 1) / (l * n)) ^ (1 / (2 * α)))) := by
  have hsqpos : ∀ m x D : ℝ, 0 ≤ m → 0 < x → 0 < D → 0 < (m + Real.sqrt (m ^ 2 + x)) / D := by
    intro m x D hm hx hD
    have : 0 < Real.sqrt (m ^ 2 + x) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hG1 : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
  refine ⟨fun lam mu nu hlam hnu => ?_, fun l m n h => ?_⟩
  · have hlp : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
    have hnp : 0 < ‖nu‖ := norm_pos_iff.mpr hnu
    rcases le_or_gt α 1 with h1 | h1
    · set ρ : ℝ := (‖mu‖ + Real.sqrt (‖mu‖ ^ 2 + (2 : ℝ) ^ (2 - max (1 - 2 * α) 0) *
          (α ^ (α - 1) * Real.Gamma α / Real.Gamma (2 * α)) * ‖lam‖ * ‖nu‖)) /
          ((2 : ℝ) ^ (1 - max (1 - 2 * α) 0) * α ^ α) with hρdef
      have hb : ∀ k : ℕ, 1 ≤ k → ‖coeff α lam mu nu k‖ ≤
          (‖nu‖ / (Real.Gamma (α + 1) * ρ)) * (k : ℝ) ^ (α - 1) * ρ ^ k :=
        coeff_bound_B_49 α hα0 h1 lam mu nu hlam hnu
      have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα0
      have hG2 : 0 < Real.Gamma (2 * α) := Real.Gamma_pos_of_pos (by linarith)
      have hρ : 0 < ρ := hsqpos _ _ _ (norm_nonneg _) (by positivity) (by positivity)
      have ht := tau_eq_le1 α hα0 h1 lam mu nu hlam hnu
      rw [← hρdef] at ht
      rw [ht]
      exact ⟨Real.rpow_pos_of_pos hρ _, radius_lower α _ ρ hα0 (by positivity) hρ _ hb⟩
    · set ρ : ℝ := (‖mu‖ + Real.sqrt (‖mu‖ ^ 2 +
          (2 : ℝ) ^ (2 * (2 - α)) * α ^ (α - 1) * ‖lam‖ * ‖nu‖ / Real.Gamma α)) / (2 * α ^ α)
        with hρdef
      have hb : ∀ k : ℕ, 1 ≤ k → ‖coeff α lam mu nu k‖ ≤
          (‖nu‖ / (Real.Gamma (α + 1) * ρ)) * (k : ℝ) ^ (α - 1) * ρ ^ k :=
        coeff_bound_B_51 α h1 hα2 lam mu nu hlam hnu
      have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα0
      have hρ : 0 < ρ := hsqpos _ _ _ (norm_nonneg _) (by positivity) (by positivity)
      have ht := tau_eq_gt1 α h1 hα2 lam mu nu hlam hnu
      rw [← hρdef] at ht
      rw [ht]
      exact ⟨Real.rpow_pos_of_pos hρ _, radius_lower α _ ρ hα0 (by positivity) hρ _ hb⟩
  · have hP : 0 < l * n := by
      rcases h with ⟨hl, hn, _⟩ | ⟨hl, hn, _⟩
      · exact mul_pos hl hn
      · exact mul_pos_of_neg_of_neg hl hn
    have hL : 0 < |l| := by rcases h with ⟨hl, _, _⟩ | ⟨hl, _, _⟩ <;> [exact abs_pos.mpr hl.ne'; exact abs_pos.mpr hl.ne]
    have hN : 0 < |n| := by rcases h with ⟨_, hn, _⟩ | ⟨_, hn, _⟩ <;> [exact abs_pos.mpr hn.ne'; exact abs_pos.mpr hn.ne]
    have hLN : |l| * |n| = l * n := by rw [← abs_mul, abs_of_pos hP]
    refine ⟨?_, ?_⟩
    · rcases h with ⟨hl, hn, hm⟩ | ⟨hl, hn, hm⟩
      · rw [abs_of_pos hl, abs_of_pos hn]
        exact (prop_B_1_b α hα0 hα2 l m n hl.le hm hn.le).2
      · have e1 : coeff α (l : ℂ) (m : ℂ) (n : ℂ) =
            fun k => -coeff α ((-l : ℝ) : ℂ) (m : ℂ) ((-n : ℝ) : ℂ) k := by
          funext k
          rw [← coeff_neg]
          push_cast
          simp
        rw [e1, radius_neg, (theorem_3_3_c α hα0 hα2 (-l) m (-n) (by linarith) (by linarith) hm).2,
          abs_of_neg hl, abs_of_neg hn]
        exact (prop_B_1_b α hα0 hα2 (-l) (-m) (-n) (by linarith) (by linarith) (by linarith)).2
    · rcases le_or_gt α 1 with h1 | h1
      · set ρ : ℝ := (5 : ℝ) ^ (1 - α) / 3 * α ^ (-α) * (|l| * |n|) / Real.Gamma (α + 1) with hρdef
        have hb : ∀ k : ℕ, 1 ≤ k → (|n| / (ρ * α * Real.Gamma α)) * ρ ^ k * (k : ℝ) ^ (α - 1) ≤
            (coeff α ((|l| : ℝ) : ℂ) 0 ((|n| : ℝ) : ℂ) (2 * k - 1)).re :=
          lower_propagation_B_1_2 α hα0 h1 |l| |n| hL hN
        have hG : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα0
        have hρ : 0 < ρ := by positivity
        refine (radius_upper α _ ρ hα0 (by positivity) hρ _
          (fun k hk => (hb k hk).trans (Complex.re_le_norm _))).trans ?_
        apply ENNReal.ofReal_le_ofReal
        rw [hρdef, upper_const_le1 α hα0 h1 _ (by positivity), hLN]
      · obtain ⟨hR1, -, hBpos⟩ := riemann_sum_B_52 α h1 hα2
        have hB1 : BTilde α ≤ 1 := by
          have h2 := hR1 2 le_rfl
          have hs : ∑ ℓ ∈ Finset.Ico (1 : ℕ) 2,
              ((fun x : ℝ => (x * (1 - x)) ^ (α - 1)) ((ℓ : ℝ) / ((2 : ℕ) : ℝ)))
              = ((1 / 2 : ℝ) * (1 - 1 / 2)) ^ (α - 1) := by
            rw [Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self, Finset.sum_empty]
            norm_num
          rw [hs] at h2
          have : ((1 / 2 : ℝ) * (1 - 1 / 2)) ^ (α - 1) ≤ 1 :=
            Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
          have : (1 / ((2 : ℕ) : ℝ)) * ((1 / 2 : ℝ) * (1 - 1 / 2)) ^ (α - 1) ≤ 1 := by
            have h0 : 0 ≤ ((1 / 2 : ℝ) * (1 - 1 / 2)) ^ (α - 1) := by positivity
            norm_num at this ⊢
            linarith
          linarith
        set ρ : ℝ := |l| * |n| * (2 * α) ^ (-α) * BTilde α / Real.Gamma (α + 1) with hρdef
        have hb : ∀ k : ℕ, 1 ≤ k → ((2 * α) ^ α / (|l| * BTilde α)) * ρ ^ k * (k : ℝ) ^ (α - 1) ≤
            (coeff α ((|l| : ℝ) : ℂ) 0 ((|n| : ℝ) : ℂ) (2 * k - 1)).re :=
          lower_propagation_B_2_2 α h1 hα2 |l| |n| hL hN
        have hρ : 0 < ρ := by positivity
        refine (radius_upper α _ ρ hα0 (by positivity) hρ _
          (fun k hk => (hb k hk).trans (Complex.re_le_norm _))).trans ?_
        apply ENNReal.ofReal_le_ofReal
        unfold CAlpha
        rw [if_neg (not_le.mpr h1), ← hLN]
        exact upper_const_gt1 α h1 _ _ (by positivity) hBpos hB1
