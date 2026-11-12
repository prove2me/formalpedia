-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_positive_C1_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:47:25.448809+00:00
-- url     : https://prove2.me/submissions/3d9e2d5f-bd86-4b12-bfe8-066155325b06

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Interior derivative floor one gives the positive-reserve secant inequality. -/
theorem solution
    (w : ℝ → ℝ) (hs : ContDiffOn ℝ 1 w (Ioi 0))
    (hg : ∀ y > 0, 1 ≤ deriv w y)
    (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    v - u ≤ w v - w u := by
  have hsubset : Icc u v ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le hu hx.1
  have hwcont : ContinuousOn w (Icc u v) :=
    hs.continuousOn.mono hsubset
  have hwdiff : DifferentiableOn ℝ w (Ioi (0 : ℝ)) :=
    hs.differentiableOn (by norm_num)
  have hcont : ContinuousOn (w - id) (Icc u v) :=
    hwcont.sub continuousOn_id
  have hdiff : DifferentiableOn ℝ (w - id) (interior (Icc u v)) := by
    rw [interior_Icc]
    have hi : Ioo u v ⊆ Ioi (0 : ℝ) := by
      intro x hx
      exact lt_trans hu hx.1
    exact (hwdiff.mono hi).sub differentiable_id.differentiableOn
  have hderiv : ∀ y ∈ interior (Icc u v), 0 ≤ deriv (w - id) y := by
    intro y hy
    have hy' : y ∈ Ioo u v := by
      simpa only [interior_Icc] using hy
    have hypos : y ∈ Ioi (0 : ℝ) := lt_trans hu hy'.1
    have hdy : DifferentiableAt ℝ w y :=
      (hwdiff y hypos).differentiableAt (isOpen_Ioi.mem_nhds hypos)
    have hsub : deriv (w - id) y = deriv w y - 1 := by
      simpa only [deriv_id] using
        (deriv_sub hdy (differentiableAt_id : DifferentiableAt ℝ (id : ℝ → ℝ) y))
    rw [hsub]
    linarith [hg y hypos]
  have hmono : MonotoneOn (w - id) (Icc u v) :=
    monotoneOn_of_deriv_nonneg (convex_Icc u v) hcont hdiff hderiv
  have hle := hmono ⟨le_refl u, huv⟩ ⟨huv, le_refl v⟩ huv
  simp only [Pi.sub_apply, id_eq] at hle
  linarith
