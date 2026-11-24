-- Prove2me | solution 1 for Formalism.mellinSgen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:01:27.900859+00:00
-- url     : https://prove2.me/submissions/f38122c0-2f84-4194-a737-58bb6f232c8e

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Theorems.Thm_Formalism_Sa_measurable
import Theorems.Thm_Formalism_Sa_eq_tsum
import Theorems.Thm_Formalism_summable_a_mxS
import Theorems.Thm_Formalism_abs_Sa_le
import Theorems.Thm_Formalism_summable_abs_a
import Theorems.Thm_Formalism_integrable_tsum_of_nonneg
import Theorems.Thm_Formalism_mxS_mellin
import Theorems.Thm_Formalism_mxS_mellin_real
import Theorems.Thm_Formalism_mxS_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution : MellinSgen := by
  intro a K hK
  have ha0 : a 0 = 0 := by
    have h := hK 0
    rw [ArithmeticFunction.map_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  refine ⟨Sa_measurable a, fun σ hσ => ?_, fun s hs => ?_⟩
  · have key := integrable_tsum_of_nonneg (μ := volume.restrict (Ioi (1 : ℝ)))
      (φ := fun n x => |a n| * (mxS n x * x ^ (-σ - 1))) (fun n => ?_) (fun n => ?_)
      (fun x => ?_) ?_
    · have hmeas : Measurable (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) := by
        have := Sa_measurable a
        fun_prop
      refine key.mono' hmeas.aestronglyMeasurable ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      have hxp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hxp)]
      calc |Sa a x| * x ^ (-σ - 1) ≤ (∑' n, |a n| * mxS n x) * x ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right (abs_Sa_le a ha0 x) hxp
        _ = ∑' n, |a n| * (mxS n x * x ^ (-σ - 1)) := by
            rw [← tsum_mul_right]; congr 1; funext n; ring
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [ha0]
      · exact ((mxS_mellin_real hn hσ).1).const_mul _
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (mxS_nonneg n x)
        (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _))
    · have ha0' : |a 0| = 0 := by simp [ha0]
      simpa only [mul_assoc] using
        (summable_a_mxS (fun n => |a n|) ha0' x).mul_right (x ^ (-σ - 1))
    · have : (fun n => ∫ x in Ioi (1 : ℝ), |a n| * (mxS n x * x ^ (-σ - 1))) =
          fun n : ℕ => |a n| * (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
        funext n
        rw [integral_const_mul]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [ha0]
        · rw [(mxS_mellin_real hn hσ).2]; ring
      rw [this]; exact (summable_abs_a a K hK hσ).div_const _
  · set F : ℕ → ℝ → ℂ := fun n x => (a n : ℂ) * ((mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) with hFdef
    have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi (1 : ℝ))) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [F, ha0]
      · exact ((mxS_mellin hn hs).1).const_mul _
    have hnorm : ∀ n, ∫ x in Ioi (1 : ℝ), ‖F n x‖ =
        |a n| * (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
      intro n
      rw [setIntegral_congr_fun measurableSet_Ioi
        (g := fun x => |a n| * (mxS n x * x ^ (-s.re - 1))) (fun x hx => ?_)]
      · rw [integral_const_mul]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [ha0]
        · rw [(mxS_mellin_real hn hs).2]; ring
      · have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
        simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mxS_nonneg n x), norm_cpow_eq_rpow_re_of_pos hx0]
        congr 3
    have hsum : Summable (fun n => ∫ x in Ioi (1 : ℝ), ‖F n x‖) := by
      simp_rw [hnorm]; exact (summable_abs_a a K hK hs).div_const _
    have hpt : ∀ x ∈ Ioi (1 : ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) = ∑' n, F n x := by
      intro x hx
      rw [Sa_eq_tsum a ha0, ofReal_tsum, ← tsum_mul_right]
      congr 1; funext n; simp only [F]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      ← integral_tsum_of_summable_integral_norm hint hsum, LSeries, ← tsum_div_const]
    congr 1; funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, ha0]
    · simp only [F]
      rw [integral_const_mul, (mxS_mellin hn hs).2, LSeries.term_of_ne_zero (by omega), cpow_neg]
      ring
end Formalism
