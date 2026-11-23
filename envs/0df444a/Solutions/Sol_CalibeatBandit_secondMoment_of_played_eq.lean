-- Prove2me | solution 1 for CalibeatBandit.secondMoment_of_played_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:57:16.759182+00:00
-- url     : https://prove2.me/submissions/80e5d0c5-a7a7-4c1f-9c70-c0caec2ec342

import Mathlib
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Definitions.Def_CalibeatBandit_rewardLoss
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_Supplement_PricingRegretBound
import Definitions.Def_CalibeatBandit_draw_run

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory

namespace DrawRun

variable {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem preDraw_le_ambient (run : DrawRun K T P) {t : ℕ} (ht : t < T) :
    run.preDraw t ≤ mΩ :=
  (run.preDraw_le_succ t ht).trans (run.info_le _ (Nat.succ_le_of_lt ht))

end DrawRun

end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix Filter
open scoped BigOperators

namespace CalibeatBandit

theorem secondMoment_of_played_eq {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ0 : 0 < μ) (hμ : μ ≤ 1 / 2)
    (hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (run : DrawRun K T P) (t : ℕ) (ht : t < T)
    (x : Ω → Fin K → ℝ) (hx : ∀ ω, IsProbVec (x ω)) (hxm : Measurable[run.preDraw t] x)
    (hplay : run.played t =ᵐ[P] fun ω => explore μ (x ω)) :
    let v := fun ω => estimate η (explore μ (x ω)) (run.I t ω) (run.obs t ω)
    let p := fun ω => explore μ (x ω)
    condExp (run.preDraw t) P (fun ω => ∑ j, x ω j * v ω j ^ 2)
      =ᵐ[P] (fun ω => ∑ j, x ω j / p ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / p ω j)) ∧
    (∀ ω, ∑ j, x ω j / p ω j *
          (run.y t ω j ^ 2 + 2 * (Real.exp 1 - 2) * η * run.y t ω j
            + (Real.exp 1 - 2) ^ 2 * η ^ 2 / p ω j) ≤ 2 * ∑ j, x ω j / p ω j) ∧
    (∀ ω, 2 * ∑ j, x ω j / p ω j ≤ 2 * K / (1 - μ)) := by
  intro v' p'
  classical
  let x' := x
  let x (j : Fin K) (ω : Ω) := x' ω j
  let p (j : Fin K) (ω : Ω) := p' ω j
  let y (j : Fin K) (ω : Ω) := run.y t ω j
  let v (j : Fin K) (ω : Ω) := v' ω j
  let d := (Real.exp 1 - 2) * η
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hm := run.preDraw_le_ambient ht
  have hx₀ (j : Fin K) (ω : Ω) : 0 ≤ x j ω := (hx ω).1 j
  have hx₁ (j : Fin K) (ω : Ω) : x j ω ≤ 1 :=
    (Finset.single_le_sum (fun k _ => hx₀ k ω) (Finset.mem_univ j)).trans_eq (hx ω).2
  have hμ₁ : μ ≤ 1 := by linarith
  have hp_eq (j : Fin K) (ω : Ω) : p j ω = (1 - μ) * x j ω + μ / K := rfl
  have hp₀ (j : Fin K) (ω : Ω) : μ / (K : ℝ) ≤ p j ω := by
    rw [hp_eq]
    exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hμ₁) (hx₀ j ω))
  have hp_pos (j : Fin K) (ω : Ω) : 0 < p j ω := (div_pos hμ0 hk).trans_le (hp₀ j ω)
  have hp_eta (j : Fin K) (ω : Ω) : 4 * η ≤ p j ω :=
    ((le_div_iff₀ hk).mpr (by nlinarith only [hKη])).trans (hp₀ j ω)
  have hη₈ : η ≤ 1 / 8 := by
    have hk₁ : 1 ≤ (K : ℝ) := by exact_mod_cast hK
    nlinarith [mul_nonneg (sub_nonneg.mpr hk₁) hη.le]
  have hd₀ : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hd₁ : d ≤ η := by
    dsimp [d]
    nlinarith [mul_nonneg (show 0 ≤ 3 - Real.exp 1 by linarith [Real.exp_one_lt_three]) hη.le]
  let indicator (j : Fin K) : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
  let a (j : Fin K) (ω : Ω) := x j ω * (y j ω ^ 2 + 2 * d * y j ω) / p j ω ^ 2
  let b (j : Fin K) (ω : Ω) := x j ω * d ^ 2 / p j ω ^ 2
  have hxm (j : Fin K) : Measurable[run.preDraw t] (x j) :=
    (measurable_pi_apply j).comp hxm
  have hym (j : Fin K) : Measurable[run.preDraw t] (y j) :=
    (measurable_pi_apply j).comp (run.y_measurable t ht)
  have hpm (j : Fin K) : Measurable[run.preDraw t] (p j) := by
    simp only [show p j = (fun ω => (1 - μ) * x j ω + μ / K) from funext (hp_eq j)]
    exact ((hxm j).const_mul _).add measurable_const
  have ham (j : Fin K) : Measurable[run.preDraw t] (a j) :=
    ((hxm j).mul (((hym j).pow_const 2).add ((hym j).const_mul _))).div ((hpm j).pow_const 2)
  have hbm (j : Fin K) : Measurable[run.preDraw t] (b j) :=
    ((hxm j).mul_const _).div ((hpm j).pow_const 2)
  have him (j : Fin K) : Measurable (indicator j) :=
    measurable_const.indicator ((run.I_measurable t ht).mono
      (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl (measurableSet_singleton j))
  let B : ℝ := (1 + 2 * d + d ^ 2) / (μ / K) ^ 2
  have hbnd (j : Fin K) (ω : Ω) : 0 ≤ a j ω ∧ 0 ≤ b j ω ∧ a j ω + b j ω ≤ B := by
    have hy := run.y_mem t ht ω j
    have hy₀ : 0 ≤ y j ω := hy.1
    have hy₁ : y j ω ≤ 1 := hy.2
    have hN : y j ω ^ 2 + 2 * d * y j ω + d ^ 2 ≤ 1 + 2 * d + d ^ 2 := by
      nlinarith [mul_nonneg hy₀ (sub_nonneg.mpr hy₁), mul_nonneg hd₀ (sub_nonneg.mpr hy₁)]
    have hx : 0 ≤ x j ω := hx₀ j ω
    refine ⟨by dsimp [a]; positivity, by dsimp [b]; positivity, ?_⟩
    dsimp [a, b, B]
    rw [← add_div, ← mul_add]
    apply div_le_div₀ (by positivity) _ (sq_pos_of_pos (div_pos hμ0 hk))
    · exact pow_le_pow_left₀ (div_nonneg hμ0.le hk.le) (hp₀ j ω) 2
    · exact (mul_le_of_le_one_left (by positivity) (hx₁ j ω)).trans hN
  have hi01 (j : Fin K) (ω : Ω) : 0 ≤ indicator j ω ∧ indicator j ω ≤ 1 := by
    by_cases h : run.I t ω = j <;> simp [indicator, h]
  have hpart (j : Fin K) : Integrable (a j * indicator j) P := by
    apply (integrable_const B).mono' (((ham j).mono hm le_rfl).mul (him j)).aestronglyMeasurable
    filter_upwards with ω
    obtain ⟨ha, hb, hab⟩ := hbnd j ω
    change ‖a j ω * indicator j ω‖ ≤ B
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha (hi01 j ω).1)]
    exact (mul_le_of_le_one_right ha (hi01 j ω).2).trans (by linarith)
  have hbint (j : Fin K) : Integrable (b j) P := by
    apply (integrable_const B).mono' ((hbm j).mono hm le_rfl).aestronglyMeasurable
    filter_upwards with ω
    obtain ⟨ha, hb, hab⟩ := hbnd j ω
    rw [Real.norm_eq_abs, abs_of_nonneg hb]
    linarith
  have hiint (j : Fin K) : Integrable (indicator j) P := by
    apply (integrable_const (1 : ℝ)).mono' (him j).aestronglyMeasurable
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hi01 j ω).1] using (hi01 j ω).2
  have hexpand (j : Fin K) (ω : Ω) :
      x j ω * v j ω ^ 2 = a j ω * indicator j ω + b j ω := by
    have hv : v j ω = (if run.I t ω = j then run.obs t ω / p j ω else 0) + d / p j ω := rfl
    rw [hv]
    by_cases h : run.I t ω = j
    · have hind : indicator j ω = 1 := by simp [indicator, h]
      have hobs : run.obs t ω = y j ω := by simp [DrawRun.obs, y, h]
      rw [if_pos h, hind, hobs, mul_one]
      dsimp [a, b]
      field_simp [(hp_pos j ω).ne']
      ring
    · have hind : indicator j ω = 0 := by simp [indicator, h]
      rw [if_neg h, hind, zero_add, mul_zero, zero_add]
      dsimp [b]
      rw [div_pow, mul_div_assoc]
  have hcond (j : Fin K) :
      condExp (run.preDraw t) P (fun ω => x j ω * v j ω ^ 2) =ᵐ[P] fun ω =>
        x j ω / p j ω * (y j ω ^ 2 + 2 * (Real.exp 1 - 2) * η * y j ω +
          (Real.exp 1 - 2) ^ 2 * η ^ 2 / p j ω) := by
    rw [show (fun ω => x j ω * v j ω ^ 2) = a j * indicator j + b j from funext (hexpand j)]
    refine (condExp_add (hpart j) (hbint j) (run.preDraw t)).trans ?_
    rw [condExp_of_stronglyMeasurable hm (hbm j).stronglyMeasurable (hbint j)]
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (ham j).stronglyMeasurable (hpart j) (hiint j),
      run.I_law t ht j, hplay] with ω hmul hlaw hpω
    change condExp (run.preDraw t) P (a j * indicator j) ω + b j ω = _
    change condExp (run.preDraw t) P (indicator j) ω = run.played t ω j at hlaw
    rw [hpω] at hlaw
    change condExp (run.preDraw t) P (indicator j) ω = p j ω at hlaw
    rw [hmul]
    change a j ω * condExp (run.preDraw t) P (indicator j) ω + b j ω = _
    rw [hlaw]
    dsimp [a, b, d]
    field_simp [(hp_pos j ω).ne']
  constructor
  · have hi (j : Fin K) : Integrable (fun ω => x j ω * v j ω ^ 2) P := by
      rw [show (fun ω => x j ω * v j ω ^ 2) = a j * indicator j + b j from funext (hexpand j)]
      exact (hpart j).add (hbint j)
    rw [show (fun ω => ∑ j, x j ω * v j ω ^ 2) = ∑ j, (fun ω => x j ω * v j ω ^ 2) by
      ext ω; simp [Finset.sum_apply]]
    refine (condExp_finsetSum (fun j _ => hi j) (run.preDraw t)).trans ?_
    have hall := ae_all_iff.mpr hcond
    filter_upwards [hall] with ω hω
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => hω j
  constructor
  · intro ω
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hy := run.y_mem t ht ω j
    have hy₀ : 0 ≤ y j ω := hy.1
    have hy₁ : y j ω ≤ 1 := hy.2
    have hdiv : d ^ 2 / p j ω ≤ η / 4 := by
      apply (div_le_iff₀ (hp_pos j ω)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hd₁) (show 0 ≤ η + d by positivity),
        mul_nonneg hη.le (sub_nonneg.mpr (hp_eta j ω))]
    have hterm : y j ω ^ 2 + 2 * d * y j ω + d ^ 2 / p j ω ≤ 2 := by
      nlinarith [mul_nonneg hy₀ (sub_nonneg.mpr hy₁), mul_nonneg hd₀ (sub_nonneg.mpr hy₁)]
    change x j ω / p j ω * (y j ω ^ 2 + 2 * (Real.exp 1 - 2) * η * y j ω +
      (Real.exp 1 - 2) ^ 2 * η ^ 2 / p j ω) ≤ 2 * (x j ω / p j ω)
    simpa only [d, mul_pow, mul_assoc, mul_comm (2 : ℝ) (x j ω / p j ω)] using
      (mul_le_mul_of_nonneg_left hterm (div_nonneg (hx₀ j ω) (hp_pos j ω).le))
  · intro ω
    have hden : 0 < 1 - μ := by linarith
    have hratio (j : Fin K) : x j ω / p j ω ≤ 1 / (1 - μ) := by
      apply (div_le_div_iff₀ (hp_pos j ω) hden).mpr
      rw [hp_eq]
      nlinarith [div_nonneg hμ0.le hk.le]
    have hsum : ∑ j, x j ω / p j ω ≤ (K : ℝ) / (1 - μ) := by
      calc
        _ ≤ ∑ _ : Fin K, (1 / (1 - μ)) := Finset.sum_le_sum fun j _ => hratio j
        _ = _ := by simp [div_eq_mul_inv]
    change 2 * (∑ j, x j ω / p j ω) ≤ 2 * (K : ℝ) / (1 - μ)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.secondMoment_of_played_eq := @CalibeatBandit.secondMoment_of_played_eq
