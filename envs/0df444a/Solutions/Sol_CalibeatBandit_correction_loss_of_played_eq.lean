-- Prove2me | solution 1 for CalibeatBandit.correction_loss_of_played_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:57:17.48434+00:00
-- url     : https://prove2.me/submissions/96a4729d-1831-4199-a6fc-39f00efcb91b

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

private theorem integrable_bounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) (B : ℝ)
    (h : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hf.aestronglyMeasurable (ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using h ω)

theorem correction_loss_of_played_eq {K T : ℕ} {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (_hKη : 4 * K * η ≤ μ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (run : DrawRun K T P)
    (x : ℕ → Ω → Fin K → ℝ) (hx : ∀ t < T, ∀ ω, IsProbVec (x t ω))
    (hxm : ∀ t < T, Measurable[run.preDraw t] (x t))
    (hplay : ∀ t < T, run.played t =ᵐ[P] fun ω => explore μ (x t ω)) :
    let v := fun t ω => estimate η (explore μ (x t ω)) (run.I t ω) (run.obs t ω)
    ∫ ω, ∑ t ∈ Finset.range T, x t ω ⬝ᵥ (v t ω - run.y t ω) ∂P
      ≤ (Real.exp 1 - 2) * η * K * T / (1 - μ) := by
  intro v
  classical
  let d := (Real.exp 1 - 2) * η
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hμ₁ : 0 < 1 - μ := by linarith
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hmin : 0 < μ / (K : ℝ) := div_pos hμ₀ hk
  let loss (t : ℕ) (j : Fin K) (ω : Ω) :=
    x t ω j * (v t ω j - run.y t ω j)
  have coordinate (t : ℕ) (ht : t < T) (j : Fin K) :
      Integrable (loss t j) P ∧ ∫ ω, loss t j ω ∂P ≤ d / (1 - μ) := by
    let x' := x
    let x : Ω → ℝ := fun ω => x' t ω j
    let p : Ω → ℝ := fun ω => explore μ (x' t ω) j
    let y : Ω → ℝ := fun ω => run.y t ω j
    let ind : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
    let a : Ω → ℝ := fun ω => x ω * y ω / p ω
    let b : Ω → ℝ := fun ω => x ω * (d / p ω - y ω)
    have hm := run.preDraw_le_ambient ht
    have hx₀ (ω : Ω) : 0 ≤ x ω := (hx t ht ω).1 j
    have hx₁ (ω : Ω) : x ω ≤ 1 :=
      (Finset.single_le_sum (fun i _ => (hx t ht ω).1 i)
        (Finset.mem_univ j)).trans_eq (hx t ht ω).2
    have hy₀ (ω : Ω) : 0 ≤ y ω := (run.y_mem t ht ω j).1
    have hy₁ (ω : Ω) : y ω ≤ 1 := (run.y_mem t ht ω j).2
    have hp_eq (ω : Ω) : p ω = (1 - μ) * x ω + μ / K := rfl
    have hp₀ (ω : Ω) : μ / (K : ℝ) ≤ p ω := by
      rw [hp_eq]
      exact le_add_of_nonneg_left (mul_nonneg hμ₁.le (hx₀ ω))
    have hp (ω : Ω) : 0 < p ω := hmin.trans_le (hp₀ ω)
    have hxm : Measurable[run.preDraw t] x :=
      (measurable_pi_apply j).comp (hxm t ht)
    have hym : Measurable[run.preDraw t] y :=
      (measurable_pi_apply j).comp (run.y_measurable t ht)
    have hpm : Measurable[run.preDraw t] p := by
      rw [funext hp_eq]
      exact (hxm.const_mul _).add measurable_const
    have ham : Measurable[run.preDraw t] a := (hxm.mul hym).div hpm
    have hbm : Measurable[run.preDraw t] b := hxm.mul ((measurable_const.div hpm).sub hym)
    have him : Measurable ind := measurable_const.indicator
      ((run.I_measurable t ht).mono (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl
        (measurableSet_singleton j))
    have hind (ω : Ω) : 0 ≤ ind ω ∧ ind ω ≤ 1 := by
      by_cases h : run.I t ω = j <;> simp [ind, h]
    have hii := integrable_bounded (P := P) him 1 fun ω => by
      simpa only [abs_of_nonneg (hind ω).1] using (hind ω).2
    have hai : Integrable (a * ind) P := by
      refine integrable_bounded ((ham.mono hm le_rfl).mul him) (1 / (μ / K)) fun ω => ?_
      change |a ω * ind ω| ≤ _
      have ha₀ : 0 ≤ a ω := div_nonneg (mul_nonneg (hx₀ ω) (hy₀ ω)) (hp ω).le
      rw [abs_of_nonneg (mul_nonneg ha₀ (hind ω).1)]
      refine (mul_le_of_le_one_right ha₀ (hind ω).2).trans ?_
      exact div_le_div₀ zero_le_one
        ((mul_le_of_le_one_left (hy₀ ω) (hx₁ ω)).trans (hy₁ ω)) hmin (hp₀ ω)
    have hbi : Integrable b P := by
      refine integrable_bounded (hbm.mono hm le_rfl) (d / (μ / K) + 1) fun ω => ?_
      have hdp : 0 ≤ d / p ω := div_nonneg hd (hp ω).le
      dsimp [b]
      rw [abs_mul, abs_of_nonneg (hx₀ ω)]
      refine (mul_le_of_le_one_left (abs_nonneg _) (hx₁ ω)).trans ?_
      exact (abs_sub _ _).trans (add_le_add
        (by rw [abs_of_nonneg hdp]; exact div_le_div₀ hd le_rfl hmin (hp₀ ω))
        (by rw [abs_of_nonneg (hy₀ ω)]; exact hy₁ ω))
    have heq : loss t j = a * ind + b := by
      funext ω
      have hv : v t ω j =
          (if run.I t ω = j then run.obs t ω / p ω else 0) + d / p ω := rfl
      change x ω * (v t ω j - y ω) = a ω * ind ω + b ω
      rw [hv]
      by_cases h : run.I t ω = j
      · have hind₁ : ind ω = 1 := by simp [ind, h]
        have hobs : run.obs t ω = y ω := by simp [DrawRun.obs, y, h]
        rw [if_pos h, hind₁, hobs]
        dsimp [a, b]
        ring
      · have hind₀ : ind ω = 0 := by simp [ind, h]
        rw [if_neg h, hind₀]
        simp [b]
    refine ⟨heq ▸ hai.add hbi, ?_⟩
    have hcond : condExp (run.preDraw t) P (loss t j) =ᵐ[P] fun ω => d * (x ω / p ω) := by
      rw [heq]
      refine (condExp_add hai hbi (run.preDraw t)).trans ?_
      rw [condExp_of_stronglyMeasurable hm hbm.stronglyMeasurable hbi]
      filter_upwards [condExp_mul_of_stronglyMeasurable_left ham.stronglyMeasurable hai hii,
        run.I_law t ht j, hplay t ht] with ω hmul hlaw hpω
      change condExp (run.preDraw t) P ind ω = run.played t ω j at hlaw
      rw [hpω] at hlaw
      change condExp (run.preDraw t) P ind ω = p ω at hlaw
      change condExp (run.preDraw t) P (a * ind) ω + b ω = _
      rw [hmul]
      change a ω * condExp (run.preDraw t) P ind ω + b ω = _
      rw [hlaw]
      dsimp [a, b]
      field_simp [(hp ω).ne']
      ring
    rw [← integral_condExp (m := run.preDraw t) hm]
    calc
      _ ≤ ∫ _ : Ω, d / (1 - μ) ∂P := by
        refine integral_mono_ae integrable_condExp (integrable_const _) ?_
        filter_upwards [hcond] with ω hω
        rw [hω, ← mul_one_div d]
        apply mul_le_mul_of_nonneg_left _ hd
        apply (div_le_div_iff₀ (hp ω) hμ₁).mpr
        rw [hp_eq, one_mul]
        linarith
      _ = _ := by simp
  have hfunction : (fun ω => ∑ t ∈ Finset.range T,
      x t ω ⬝ᵥ (v t ω - run.y t ω)) =
      fun ω => ∑ t ∈ Finset.range T, ∑ j, loss t j ω := by
    funext ω
    simp only [dotProduct, Pi.sub_apply, loss]
  rw [hfunction]
  rw [integral_finsetSum (Finset.range T)
    (f := fun t ω => ∑ j, loss t j ω) (fun t ht => integrable_finsetSum _ fun j _ =>
      (coordinate t (Finset.mem_range.mp ht) j).1)]
  calc
    _ ≤ ∑ _ ∈ Finset.range T, ∑ _ : Fin K, d / (1 - μ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [integral_finsetSum _ fun j _ => (coordinate t (Finset.mem_range.mp ht) j).1]
      exact Finset.sum_le_sum fun j _ => (coordinate t (Finset.mem_range.mp ht) j).2
    _ = _ := by simp [d, div_eq_mul_inv]; ring

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.correction_loss_of_played_eq := @CalibeatBandit.correction_loss_of_played_eq
