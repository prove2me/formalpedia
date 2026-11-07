-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn17_factor_derivative_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:46:51.412391+00:00
-- url     : https://prove2.me/submissions/42363965-0123-47b9-bd67-bb4a74de6f02

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_first_order_exp_comparison_v2
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (rpos rneg : ℝ) (hrpos : 0 < rpos) (hrneg : rneg < 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hODE : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      iteratedDeriv 2 w y - (rpos + rneg) * deriv w y + rpos * rneg * w y ≤ 0) :
    ∀ y : ℝ, 1 ≤ y →
      deriv w y - rpos * w y ≤
        (deriv w 1 - rpos * w 1) * Real.exp (rneg * (y - 1)) := by
  have hSmooth : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)) :=
    hw_smooth.mono (by
      intro t ht
      change 0 < t at ht
      change 0 < t ∧ ENNReal.ofReal t < C
      exact ⟨ht, by simp [hTop]⟩)
  have hDerivSmooth : ContDiffOn ℝ 1 (deriv w) (Ioi (0 : ℝ)) :=
    hSmooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hwDiff : DifferentiableOn ℝ w (Ioi (0 : ℝ)) :=
    hSmooth.differentiableOn (by norm_num)
  have hddDiff : DifferentiableOn ℝ (deriv w) (Ioi (0 : ℝ)) :=
    hDerivSmooth.differentiableOn (by norm_num)
  have hwContOne : ContinuousOn w (Ici (1 : ℝ)) :=
    hw_cont.mono (by
      intro t ht
      exact mem_Ici.mpr (by have := mem_Ici.mp ht; linarith))
  have hddContOne : ContinuousOn (deriv w) (Ici (1 : ℝ)) :=
    hDerivSmooth.continuousOn.mono (by
      intro t ht
      exact mem_Ioi.mpr (by have := mem_Ici.mp ht; linarith))
  let g : ℝ → ℝ := fun t => deriv w t - rpos * w t
  have hgCont : ContinuousOn g (Ici (1 : ℝ)) :=
    hddContOne.sub (hwContOne.const_mul rpos)
  have hIter : ∀ t : ℝ, iteratedDeriv 2 w t = deriv (deriv w) t := by
    intro t
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ]
    simp
  have hgHasDeriv : ∀ t : ℝ, 1 < t →
      HasDerivAt g (iteratedDeriv 2 w t - rpos * deriv w t) t := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hFirst : HasDerivAt w (deriv w t) t :=
      (hwDiff.differentiableAt (isOpen_Ioi.mem_nhds ht0)).hasDerivAt
    have hSecond : HasDerivAt (deriv w) (deriv (deriv w) t) t :=
      (hddDiff.differentiableAt (isOpen_Ioi.mem_nhds ht0)).hasDerivAt
    have hTerm := hSecond.sub (hFirst.const_mul rpos)
    change HasDerivAt (fun s : ℝ => deriv w s - rpos * w s)
      (deriv (deriv w) t - rpos * deriv w t) t at hTerm
    simpa only [g, ← hIter t] using hTerm
  have hgDiff : DifferentiableOn ℝ g (Ioi (1 : ℝ)) := by
    intro t ht
    exact (hgHasDeriv t ht).differentiableAt.differentiableWithinAt
  have hgODE : ∀ t : ℝ, 1 < t → deriv g t ≤ rneg * g t := by
    intro t ht
    have hEq := (hgHasDeriv t ht).deriv
    have hOriginal := hODE t (by linarith) (by simp [hTop])
    rw [hEq]
    dsimp [g]
    nlinarith [hOriginal]
  have hComp :=
    AvramDividend.Classical.avram_p4_f4_turn16_first_order_exp_comparison_v2
      g rneg 1 hgCont hgDiff hgODE
  intro y hy
  simpa only [g] using hComp y hy
