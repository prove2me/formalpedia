-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:39:59.637857+00:00
-- url     : https://prove2.me/submissions/275cb1e9-f1b6-4549-b5c9-88386f9bb179

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Tail primitive of the majorant** (Letwin Lemma A.4, p. 17, `q_R(t) = R⁻¹ ∫_{t/R}^∞ w`): for smooth nonnegative
`w` vanishing for `t ≤ 0` and `t ≥ 3` and `R > 0`, `q_R t = R⁻¹ ∫_{t/R}^3 w` is smooth with `q_R′ t = −R⁻² w(t/R)`,
`0 ≤ q_R ≤ R⁻¹ ∫_0^3 w`, and `q_R t = 0` for `t ≥ 3R`. -/
theorem solution {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hw0 : ∀ t, 0 ≤ w t) (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun t => R⁻¹ * ∫ s in t / R..3, w s) ∧
      (∀ t, deriv (fun t => R⁻¹ * ∫ s in t / R..3, w s) t = -((R ^ 2)⁻¹ * w (t / R))) ∧
      (∀ t, 0 ≤ R⁻¹ * ∫ s in t / R..3, w s) ∧
      (∀ t, R⁻¹ * ∫ s in t / R..3, w s ≤ R⁻¹ * ∫ s in (0 : ℝ)..3, w s) ∧
      (∀ t, 3 * R ≤ t → R⁻¹ * ∫ s in t / R..3, w s = 0) := by
      let q : ℝ → ℝ := fun t => R⁻¹ * ∫ s in t / R..3, w s

      have hR0 : R ≠ 0 := ne_of_gt hR
      have hRinv : 0 ≤ R⁻¹ := le_of_lt (inv_pos.mpr hR)

      have hF : ∀ t : ℝ,
          HasDerivAt (fun t : ℝ => ∫ s in t..3, w s) (-w t) t := by
        intro t
        exact intervalIntegral.integral_hasDerivAt_left
          (hw.continuous.intervalIntegrable t 3)
          (hw.continuous.stronglyMeasurableAtFilter MeasureTheory.volume (nhds t))
          hw.continuous.continuousAt

      have hq_deriv : ∀ t : ℝ,
          HasDerivAt q (-((R ^ 2)⁻¹ * w (t / R))) t := by
        intro t
        change HasDerivAt
          (fun t : ℝ => R⁻¹ * ∫ s in t / R..3, w s)
          (-((R ^ 2)⁻¹ * w (t / R))) t
        have hcoef :
            R⁻¹ * ((-w (t / R)) * (1 / R)) =
              -((R ^ 2)⁻¹ * w (t / R)) := by
          field_simp [hR0]
        have h :=
          ((hF (t / R)).comp t ((hasDerivAt_id t).div_const R)).const_mul R⁻¹
        simpa only [Function.comp_apply, id_eq, hcoef] using h

      have hq_diff : Differentiable ℝ q := by
        intro t
        exact (hq_deriv t).differentiableAt

      have hderiv_eq :
          deriv q = fun t : ℝ => -((R ^ 2)⁻¹ * w (t / R)) := by
        funext t
        exact (hq_deriv t).deriv

      have hcomp : ContDiff ℝ ∞ (fun t => w (t / R)) := by
        exact hw.comp (contDiff_id.div_const R)

      have hexpl :
          ContDiff ℝ ∞ (fun t => -((R ^ 2)⁻¹ * w (t / R))) := by
        simpa only [smul_eq_mul, Function.comp_def, id_eq] using
          (ContDiff.const_smul ((R ^ 2)⁻¹) hcomp).neg

      have hq_smooth : ContDiff ℝ ∞ q := by
        exact contDiff_infty_iff_deriv.mpr
          ⟨hq_diff, by rw [hderiv_eq]; exact hexpl⟩

      have hleft (a : ℝ) (ha : a ≤ 0) :
          (∫ s in a..0, w s) = 0 := by
        calc
          (∫ s in a..0, w s) =
              ∫ s in a..0, (fun _ : ℝ => 0) s := by
                apply intervalIntegral.integral_congr
                intro x hx
                have hx' : x ∈ Set.Icc a 0 := by
                  simpa [Set.uIcc_of_le ha] using hx
                simpa using hws x (Or.inl hx'.2)
          _ = 0 := by simp

      have hright (b : ℝ) (hb : 3 ≤ b) :
          (∫ s in 3..b, w s) = 0 := by
        calc
          (∫ s in 3..b, w s) =
              ∫ s in 3..b, (fun _ : ℝ => 0) s := by
                apply intervalIntegral.integral_congr
                intro x hx
                have hx' : x ∈ Set.Icc 3 b := by
                  simpa [Set.uIcc_of_le hb] using hx
                simpa using hws x (Or.inr hx'.1)
          _ = 0 := by simp

      have hnonneg (a b : ℝ) (hab : a ≤ b) :
          0 ≤ (∫ s in a..b, w s) := by
        exact intervalIntegral.integral_nonneg hab (fun x _ => hw0 x)

      have hzero_ge (a : ℝ) (ha : 3 ≤ a) :
          (∫ s in a..3, w s) = 0 := by
        calc
          (∫ s in a..3, w s) = -(∫ s in 3..a, w s) :=
            intervalIntegral.integral_symm 3 a
          _ = 0 := by rw [hright a ha]; simp

      have hadd (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
          (∫ s in a..c, w s) =
            (∫ s in a..b, w s) + ∫ s in b..c, w s := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals
          (hw.continuous.intervalIntegrable a b)
          (hw.continuous.intervalIntegrable b c)

      have hupper (a : ℝ) :
          (∫ s in a..3, w s) ≤ ∫ s in (0 : ℝ)..3, w s := by
        by_cases ha : a ≤ 0
        · calc
            (∫ s in a..3, w s) =
                (∫ s in a..0, w s) + ∫ s in (0 : ℝ)..3, w s :=
              hadd a 0 3 ha (by norm_num)
            _ ≤ ∫ s in (0 : ℝ)..3, w s := by
              simpa only [hleft a ha, zero_add] using
                (le_refl (∫ s in (0 : ℝ)..3, w s))
        · have ha0 : 0 ≤ a := le_of_not_ge ha
          by_cases h3 : 3 ≤ a
          · have htot : 0 ≤ ∫ s in (0 : ℝ)..3, w s :=
              hnonneg 0 3 (by norm_num)
            rw [hzero_ge a h3]
            linarith
          · have ha3 : a ≤ 3 := le_of_not_ge h3
            have hnon : 0 ≤ (∫ s in (0 : ℝ)..a, w s) :=
              hnonneg 0 a ha0
            have heq :
                (∫ s in (0 : ℝ)..3, w s) =
                  (∫ s in (0 : ℝ)..a, w s) + ∫ s in a..3, w s :=
              hadd 0 a 3 ha0 ha3
            rw [heq]
            linarith

      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [q] using hq_smooth
      · intro t
        simpa [q] using (hq_deriv t).deriv
      · intro t
        rcases le_total (t / R) 3 with ht | ht
        · exact mul_nonneg hRinv (hnonneg (t / R) 3 ht)
        · rw [hzero_ge (t / R) ht]
          simp
      · intro t
        exact mul_le_mul_of_nonneg_left (hupper (t / R)) hRinv
      · intro t ht
        have ht' : 3 ≤ t / R := by
          exact (le_div_iff₀ hR).2 ht
        change R⁻¹ * ∫ s in t / R..3, w s = 0
        rw [hzero_ge (t / R) ht']
        simp
