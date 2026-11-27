-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_secant_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:42:41.738445+00:00
-- url     : https://prove2.me/submissions/884489ff-8f95-40c6-a347-838418d58262

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_mean_value
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (a b : ℕ → ℝ) (A B : ℝ)
    (hab : ∀ n, b n ≤ a n) (hAB : B ≤ A)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    Tendsto (fun n => Q (a n) (b n)) atTop (𝓝 (Q A B)) := by 
  classical
  dsimp only
  by_cases he : A = B
  · subst B
    choose c hc hQ using fun n => avram_locmoll_band_secant_mean_value g hg (a n) (b n) (hab n)
    have ht : Tendsto c atTop (𝓝 A) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hb ha (fun n => (hc n).1) (fun n => (hc n).2)
    have hd : Tendsto (fun n => deriv g (c n)) atTop (𝓝 (deriv g A)) :=
      (hg.continuous_deriv (by norm_num)).continuousAt.tendsto.comp ht
    simpa only [if_pos rfl, if_true] using hd.congr (fun n => hQ n)
  · have hlt : B < A := lt_of_le_of_ne hAB (Ne.symm he)
    have hn : ∀ᶠ n in atTop, a n ≠ b n :=
      (hb.eventually_lt ha hlt).mono (fun n hn => ne_of_gt hn)
    have ht := ((hg.continuous.continuousAt.tendsto.comp ha).sub
      (hg.continuous.continuousAt.tendsto.comp hb)).div (ha.sub hb) (sub_ne_zero.mpr he)
    rw [if_neg he]
    exact ht.congr' (hn.mono (fun n hn => (if_neg hn).symm))
