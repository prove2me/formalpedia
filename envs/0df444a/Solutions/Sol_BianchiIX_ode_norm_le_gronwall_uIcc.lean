-- Prove2me | solution 1 for BianchiIX.ode_norm_le_gronwall_uIcc
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:06:20.873702+00:00
-- url     : https://prove2.me/submissions/8e2eced5-6fa7-4c08-bb33-7d1c5ee2d5f6

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter Metric Asymptotics
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem solution {f df : ℝ → E} {t₀ t δ K ε : ℝ}
    (hf : ∀ u ∈ uIcc t₀ t, HasDerivAt f (df u) u) (hinit : ‖f t₀‖ ≤ δ)
    (hbound : ∀ u ∈ uIcc t₀ t, ‖df u‖ ≤ K * ‖f u‖ + ε) :
    ‖f t‖ ≤ gronwallBound δ K ε |t - t₀| := by
  by_cases htt : t₀ ≤ t
  · rw [uIcc_of_le htt] at hf hbound
    simpa only [abs_of_nonneg (sub_nonneg.mpr htt)] using
      norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivAt.continuousOn hf)
        (fun u hu => (hf u (Ico_subset_Icc_self hu)).hasDerivWithinAt) hinit
        (fun u hu => hbound u (Ico_subset_Icc_self hu)) t ⟨htt, le_rfl⟩
  · have hrev (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) : t₀ - u ∈ uIcc t₀ t := by
      rw [uIcc_of_ge (le_of_not_ge htt)]
      constructor <;> linarith [hu.1, hu.2]
    have hg (u : ℝ) (hu : u ∈ Icc 0 (t₀ - t)) :
        HasDerivAt (fun v => f (t₀ - v)) (-df (t₀ - u)) u := by
      convert! (hf (t₀ - u) (hrev u hu)).scomp u ((hasDerivAt_id u).const_sub t₀) using 1
      simp
    have H := norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivAt.continuousOn hg)
      (fun u hu => (hg u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
      (δ := δ) (K := K) (ε := ε) (by simpa using hinit)
      (fun u hu => by simpa using hbound (t₀ - u) (hrev u (Ico_subset_Icc_self hu)))
      (t₀ - t) ⟨by linarith, le_rfl⟩
    simpa [abs_of_neg (sub_neg.mpr (lt_of_not_ge htt)), neg_sub] using H
