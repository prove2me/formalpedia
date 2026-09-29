-- Prove2me | solution 1 for Complex.tsum_one_div_add_int_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/52e68499-4269-5ea6-9f12-4002e2f9b27f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_tsum_one_div_add_int_pow_four

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Real Topology
open Complex Filter Set Topology

noncomputable section

namespace HurwitzFour

def F (w : ℂ) : ℂ := ∑' n : ℤ, 1 / (w + n) ^ 4

def R (w : ℂ) : ℂ :=
  (2 * π * I) ^ 4 / 6 *
    (cexp (2 * π * I * w) * (cexp (2 * π * I * w) ^ 2 + 4 * cexp (2 * π * I * w) + 1) /
      (1 - cexp (2 * π * I * w)) ^ 4)

theorem natCast_pow_three_eq (n : ℕ) :
    ((n : ℕ) : ℂ) ^ 3 = (((n + 3).choose 3 : ℕ) : ℂ) * 6 - (((n + 2).choose 2 : ℕ) : ℂ) * 12 +
      (((n + 1).choose 1 : ℕ) : ℂ) * 7 - 1 := by
  have h3N : (n + 3).choose 3 * 6 = (n + 1) * (n + 2) * (n + 3) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 3
    have hd : (n + 3).descFactorial 3 = (n + 3) * (n + 2) * (n + 1) := by
      simp [Nat.descFactorial_zero]
      ring
    have hf : (3 : ℕ).factorial = 6 := rfl
    rw [hd, hf] at h
    linarith [h]
  have h2N : (n + 2).choose 2 * 2 = (n + 1) * (n + 2) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (n + 2) 2
    have hd : (n + 2).descFactorial 2 = (n + 2) * (n + 1) := by
      simp [Nat.descFactorial_zero]
      ring
    have hf : (2 : ℕ).factorial = 2 := rfl
    rw [hd, hf] at h
    linarith [h]
  have h1N : (n + 1).choose 1 = n + 1 := Nat.choose_one_right _
  have h3C : (((n + 3).choose 3 : ℕ) : ℂ) * 6 = (n + 1) * (n + 2) * (n + 3) := by exact_mod_cast h3N
  have h2C : (((n + 2).choose 2 : ℕ) : ℂ) * 2 = (n + 1) * (n + 2) := by exact_mod_cast h2N
  have h1C : (((n + 1).choose 1 : ℕ) : ℂ) = n + 1 := by exact_mod_cast h1N
  linear_combination (-1 : ℂ) * h3C + 6 * h2C + (-7 : ℂ) * h1C

theorem geom_value_identity {r : ℂ} (h : 1 - r ≠ 0) :
    6 * (1 / (1 - r) ^ 4) - 12 * (1 / (1 - r) ^ 3) + 7 * (1 / (1 - r) ^ 2) - 1 / (1 - r) ^ 1 =
      r * (r ^ 2 + 4 * r + 1) / (1 - r) ^ 4 := by
  field_simp
  ring

theorem hasSum_pow_three_mul_geometric {r : ℂ} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ ↦ (n : ℂ) ^ 3 * r ^ n) (r * (r ^ 2 + 4 * r + 1) / (1 - r) ^ 4) := by
  have h3 := hasSum_choose_mul_geometric_of_norm_lt_one 3 hr
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 hr
  have h0 := hasSum_choose_mul_geometric_of_norm_lt_one 0 hr
  have hr1 : (1 : ℂ) - r ≠ 0 := by
    intro h
    have : r = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at hr
    exact lt_irrefl _ hr
  have H := (((h3.mul_left 6).sub (h2.mul_left 12)).add (h1.mul_left 7)).sub h0
  convert H using 1
  · rfl
  · funext n
    rw [natCast_pow_three_eq n]
    simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one]
    ring
  · rw [← geom_value_identity hr1]

theorem F_eq_R_of_im_pos {w : ℂ} (hw : 0 < w.im) : F w = R w := by
  let z : UpperHalfPlane := ⟨w, hw⟩
  have hL := EisensteinSeries.qExpansion_identity (k := 3) (by norm_num) z
  have hq : ‖cexp (2 * π * I * (z : ℂ))‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have hS := (hasSum_pow_three_mul_geometric hq).tsum_eq
  have hz : ((z : ℂ)) = w := rfl
  rw [hz] at hL hS
  have h4 : ∀ n : ℤ, 1 / ((w : ℂ) + n) ^ (3 + 1) = 1 / (w + n) ^ 4 := fun n ↦ by norm_num
  simp only [h4] at hL
  rw [F, hL, hS, R]
  have hf : ((3 : ℕ).factorial : ℂ) = 6 := by
    rw [show (3 : ℕ).factorial = 6 from rfl]; norm_num
  rw [hf]
  ring

theorem isClosed_range_intCast : IsClosed (Set.range ((↑) : ℤ → ℂ)) := by
  have h : IsClosedEmbedding (fun n : ℤ ↦ (((n : ℝ)) : ℂ)) :=
    Complex.isometry_ofReal.isClosedEmbedding.comp Int.isClosedEmbedding_coe_real
  have hr : Set.range (fun n : ℤ ↦ (((n : ℝ)) : ℂ)) = Set.range ((↑) : ℤ → ℂ) := by
    ext w; simp
  exact hr ▸ h.isClosed_range

theorem isOpen_integerComplement : IsOpen integerComplement :=
  isClosed_range_intCast.isOpen_compl

theorem exists_pos_le_norm_add_intCast {w : ℂ} (hw : w ∈ integerComplement) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℤ, d ≤ ‖w + n‖ := by
  have hne : (Set.range ((↑) : ℤ → ℂ)).Nonempty := ⟨0, 0, by simp⟩
  have hw' : w ∉ Set.range ((↑) : ℤ → ℂ) := hw
  refine ⟨Metric.infDist w (Set.range ((↑) : ℤ → ℂ)),
    (isClosed_range_intCast.notMem_iff_infDist_pos hne).mp hw', fun n ↦ ?_⟩
  have h := Metric.infDist_le_dist_of_mem (x := w) (show ((-n : ℤ) : ℂ) ∈ Set.range ((↑) : ℤ → ℂ) from ⟨-n, rfl⟩)
  rw [dist_eq_norm, Int.cast_neg, sub_neg_eq_add] at h
  exact h

theorem summable_norm_term (w : ℂ) : Summable fun n : ℤ ↦ 1 / ‖w + n‖ ^ 4 := by
  have h := EisensteinSeries.linear_right_summable w 1 (k := 4) (by norm_num)
  have h' := summable_norm_iff.mpr h
  refine h'.congr fun n ↦ ?_
  simp only [Int.cast_one, one_mul, norm_inv, norm_pow, zpow_ofNat, one_div]

theorem differentiableAt_F {w₀ : ℂ} (hw₀ : w₀ ∈ integerComplement) : DifferentiableAt ℂ F w₀ := by
  obtain ⟨d, hd, hdle⟩ := exists_pos_le_norm_add_intCast hw₀
  have hpos : ∀ n : ℤ, 0 < ‖w₀ + n‖ := fun n ↦ hd.trans_le (hdle n)
  set S : Set ℂ := Metric.ball w₀ (d / 2) with hS
  have hSo : IsOpen S := Metric.isOpen_ball
  have hlow : ∀ n : ℤ, ∀ w ∈ S, ‖w₀ + n‖ / 2 ≤ ‖w + n‖ := by
    intro n w hw
    have h1 : ‖w - w₀‖ < d / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have h2 : ‖w₀ + n‖ ≤ ‖w + n‖ + ‖w - w₀‖ := by
      calc ‖w₀ + (n : ℂ)‖ = ‖(w + n) - (w - w₀)‖ := by ring_nf
        _ ≤ ‖w + n‖ + ‖w - w₀‖ := norm_sub_le _ _
    linarith [hdle n]
  have hne : ∀ n : ℤ, ∀ w ∈ S, (w + n) ≠ 0 := by
    intro n w hw h
    have := hlow n w hw
    rw [h, norm_zero] at this
    linarith [hpos n]
  have hF : DifferentiableOn ℂ (fun w : ℂ ↦ ∑' n : ℤ, 1 / (w + (n : ℂ)) ^ 4) S := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun n : ℤ ↦ 16 * (1 / ‖w₀ + n‖ ^ 4))
      ((summable_norm_term w₀).mul_left 16) (fun n ↦ ?_) hSo (fun n w hw ↦ ?_)
    · apply DifferentiableOn.div (differentiableOn_const _) (by fun_prop)
      intro w hw
      exact pow_ne_zero _ (hne n w hw)
    · have hwn : 0 < ‖w + n‖ := norm_pos_iff.mpr (hne n w hw)
      rw [norm_div, norm_one, norm_pow]
      have hle : ‖w₀ + n‖ ^ 4 ≤ 16 * ‖w + n‖ ^ 4 := by
        have := hlow n w hw
        have h0 : 0 ≤ ‖w₀ + (n : ℂ)‖ := norm_nonneg _
        nlinarith [pow_le_pow_left₀ (by positivity) this 4]
      have ha : 0 < ‖w₀ + (n : ℂ)‖ ^ 4 := pow_pos (hpos n) 4
      have hb : 0 < ‖w + (n : ℂ)‖ ^ 4 := pow_pos hwn 4
      show 1 / ‖w + (n : ℂ)‖ ^ 4 ≤ 16 * (1 / ‖w₀ + (n : ℂ)‖ ^ 4)
      rw [show (16 : ℝ) * (1 / ‖w₀ + (n : ℂ)‖ ^ 4) = 16 / ‖w₀ + (n : ℂ)‖ ^ 4 by ring,
        div_le_div_iff₀ hb ha]
      linarith
  exact hF.differentiableAt (hSo.mem_nhds (Metric.mem_ball_self (half_pos hd)))

theorem differentiableOn_F : DifferentiableOn ℂ F integerComplement :=
  fun w hw ↦ (differentiableAt_F hw).differentiableWithinAt

theorem cexp_ne_one {w : ℂ} (hw : w ∈ integerComplement) : cexp (2 * π * I * w) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have h3 : w * (2 * π * I) = n * (2 * π * I) := by rw [mul_comm]; exact hn
  exact hw ⟨n, (mul_right_cancel₀ h2 h3).symm⟩

theorem differentiableOn_R : DifferentiableOn ℂ R integerComplement := by
  intro w hw
  have hne : (1 - cexp (2 * π * I * w)) ^ 4 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (cexp_ne_one hw).symm)
  apply DifferentiableAt.differentiableWithinAt
  unfold R
  fun_prop (disch := exact hne)

theorem isPreconnected_integerComplement : IsPreconnected integerComplement := by
  have h : IsConnected (Set.range ((↑) : ℤ → ℂ))ᶜ :=
    Set.Countable.isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) (Set.countable_range _)
  exact h.isPreconnected

theorem F_eq_R {w : ℂ} (hw : w ∈ integerComplement) : F w = R w := by
  have hF : AnalyticOnNhd ℂ F integerComplement := differentiableOn_F.analyticOnNhd isOpen_integerComplement
  have hR : AnalyticOnNhd ℂ R integerComplement := differentiableOn_R.analyticOnNhd isOpen_integerComplement
  have hI : (I : ℂ) ∈ integerComplement := by
    have := UpperHalfPlane.coe_mem_integerComplement ⟨I, by simp⟩
    simpa using this
  have hev : F =ᶠ[𝓝 (I : ℂ)] R := by
    have ho : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [ho.mem_nhds (show (0 : ℝ) < (I : ℂ).im by simp)] with w hw
    exact F_eq_R_of_im_pos hw
  exact hF.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_integerComplement hI hev hw

end HurwitzFour

end

open HurwitzFour in
theorem solution (x : ℝ) (hx : ∀ n : ℤ, (x : ℝ) ≠ n) :
    ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ 4 =
      (2 * π * I) ^ 4 / 6 *
        (Complex.exp (2 * π * I * x) * (Complex.exp (2 * π * I * x) ^ 2 + 4 * Complex.exp (2 * π * I * x) + 1) /
          (1 - Complex.exp (2 * π * I * x)) ^ 4) := by
  have hxC : (x : ℂ) ∈ integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    apply hx n
    have : ((n : ℝ) : ℂ) = (x : ℂ) := by rw [← hn]; simp
    exact_mod_cast this.symm
  exact F_eq_R hxC

end S_Complex_tsum_one_div_add_int_pow_four
end P2MW
export P2MW.S_Complex_tsum_one_div_add_int_pow_four (solution)
