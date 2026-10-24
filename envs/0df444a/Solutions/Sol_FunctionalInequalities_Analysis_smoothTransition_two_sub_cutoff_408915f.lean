-- Prove2me | solution 1 for FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:20:02.804989+00:00
-- url     : https://prove2.me/submissions/a1292c8f-57fb-44d5-b582-ba58350e0f3d

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
/-- **The cutoff profile** `η t = smoothTransition (2 − t)` (Letwin Lemma A.4, p. 17): smooth, antitone, with values in
`[0, 1]`, equal to `1` on `t ≤ 1` and to `0` on `t ≥ 2`; `η′` and `η″` vanish off `[1, 2]`, are compactly supported and
share a finite bound `B`. -/
theorem solution :
    ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 - s)) ∧ Antitone (fun s : ℝ => Real.smoothTransition (2 - s)) ∧
      (∀ t : ℝ, 0 ≤ Real.smoothTransition (2 - t) ∧ Real.smoothTransition (2 - t) ≤ 1) ∧
      (∀ t : ℝ, t ≤ 1 → Real.smoothTransition (2 - t) = 1) ∧
      (∀ t : ℝ, 2 ≤ t → Real.smoothTransition (2 - t) = 0) ∧
      (∀ t : ℝ, t < 1 ∨ 2 < t →
        deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t = 0 ∧ deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t = 0) ∧
      HasCompactSupport (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) ∧
      HasCompactSupport (deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s)))) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
        |deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t| ≤ B ∧ |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ B := by
  classical
  let f : ℝ → ℝ := fun s => Real.smoothTransition (2 - s)
  have hf : ContDiff ℝ ∞ f :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  have hleft (t : ℝ) (ht : t ≤ 1) : f t = 1 := by
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have hright (t : ℝ) (ht : 2 ≤ t) : f t = 0 := by
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  have hd (t : ℝ) (ht : t < 1 ∨ 2 < t) : deriv f t = 0 := by
    rcases ht with ht | ht
    · have he : f =ᶠ[nhds t] (fun _ : ℝ => (1 : ℝ)) := by
        filter_upwards [eventually_lt_nhds ht] with s hs
        exact hleft s hs.le
      calc
        deriv f t = deriv (fun _ : ℝ => (1 : ℝ)) t := he.deriv_eq
        _ = 0 := by simp
    · have he : f =ᶠ[nhds t] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [eventually_gt_nhds ht] with s hs
        exact hright s hs.le
      calc
        deriv f t = deriv (fun _ : ℝ => (0 : ℝ)) t := he.deriv_eq
        _ = 0 := by simp
  have hdd (t : ℝ) (ht : t < 1 ∨ 2 < t) :
      deriv (deriv f) t = 0 := by
    have he : deriv f =ᶠ[nhds t] (fun _ : ℝ => (0 : ℝ)) := by
      rcases ht with ht | ht
      · filter_upwards [eventually_lt_nhds ht] with s hs
        exact hd s (Or.inl hs)
      · filter_upwards [eventually_gt_nhds ht] with s hs
        exact hd s (Or.inr hs)
    calc
      deriv (deriv f) t = deriv (fun _ : ℝ => (0 : ℝ)) t := he.deriv_eq
      _ = 0 := by simp
  have hout (t : ℝ) (ht : t ∉ Set.Icc (1 : ℝ) 2) :
      t < 1 ∨ 2 < t := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using ht
  have hc : HasCompactSupport (deriv f) := by
    apply HasCompactSupport.intro
      (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
    intro t ht
    exact hd t (hout t ht)
  have hcc : HasCompactSupport (deriv (deriv f)) := hc.deriv
  have hca : HasCompactSupport (fun t => |deriv f t|) := by
    apply HasCompactSupport.intro
      (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
    intro t ht
    rw [hd t (hout t ht), abs_zero]
  have hcca : HasCompactSupport (fun t => |deriv (deriv f) t|) := by
    apply HasCompactSupport.intro
      (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2))
    intro t ht
    rw [hdd t (hout t ht), abs_zero]
  have hfd : ContDiff ℝ ∞ (deriv f) := by
    simpa using hf.iterate_deriv 1
  have hdcont : Continuous (deriv f) := by
    exact hf.continuous_deriv (by simp)
  have hddcont : Continuous (deriv (deriv f)) := by
    exact hfd.continuous_deriv (by simp)
  obtain ⟨B₁, hB₁⟩ := hdcont.abs.bounded_above_of_compact_support hca
  obtain ⟨B₂, hB₂⟩ := hddcont.abs.bounded_above_of_compact_support hcca
  have hb₁ (t : ℝ) : |deriv f t| ≤ B₁ := by
    simpa [Real.norm_eq_abs, abs_abs] using hB₁ t
  have hb₂ (t : ℝ) : |deriv (deriv f) t| ≤ B₂ := by
    simpa [Real.norm_eq_abs, abs_abs] using hB₂ t
  refine ⟨hf, ?_, ?_, hleft, hright, ?_, hc, hcc, ?_⟩
  · apply Real.smoothTransition.monotone.comp_antitone
    intro a b hab
    linarith
  · intro t
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro t ht
    exact ⟨hd t ht, hdd t ht⟩
  · refine ⟨max 0 (max B₁ B₂), le_max_left _ _, ?_⟩
    intro t
    exact
      ⟨(hb₁ t).trans ((le_max_left B₁ B₂).trans (le_max_right _ _)),
        (hb₂ t).trans ((le_max_right B₁ B₂).trans (le_max_right _ _))⟩
