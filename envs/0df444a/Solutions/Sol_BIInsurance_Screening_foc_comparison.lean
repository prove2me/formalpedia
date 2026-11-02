-- Prove2me | solution 1 for BIInsurance.Screening.foc_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:04:06.856068+00:00
-- url     : https://prove2.me/submissions/25e8d143-2318-4322-88e6-0f1e8b586107

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening.FocCmp

open BIInsurance.Screening

lemma Exi_lt (P : Params) (hS : P.Standing) : Exi P P.muL < Exi P P.muH := by
  have hmu : P.muL < P.muH := hS.2.2.2.1
  have hβ0 : 0 < P.β := hS.2.2.2.2.2.2.1
  have hβ1 : P.β < 1 := hS.2.2.2.2.2.2.2.1
  have hγ : 0 < P.γ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have key : ∀ d : ℝ, xi P P.K P.muL d < xi P P.K P.muH d := by
    intro d
    unfold xi
    apply Real.log_lt_log (by positivity)
    have : (P.muL + d) / P.γ < (P.muH + d) / P.γ := by
      apply div_lt_div_of_pos_right _ hγ; linarith
    have := Real.exp_lt_exp.mpr this
    linarith
  unfold Exi
  have h1 := key P.dH
  have h2 := key P.dL
  nlinarith

theorem main (P : Params) (hS : P.Standing) (s : ℝ) (h57 : foc57 P s = 0) :
    foc56 P s < 0 := by
  have hα0 : 0 < P.α := hS.2.2.2.2.2.2.2.2.2.1
  have hα1 : P.α < 1 := hS.2.2.2.2.2.2.2.2.2.2.1
  have hγ : 0 < P.γ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have hlam : 0 < P.lam := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hE := Exi_lt P hS
  have key : foc56 P s = P.γ * (Exi P P.muL - Exi P P.muH)
      * ((1 - P.α) * (1 + P.lam) + P.α * P.lam) := by
    unfold foc57 at h57
    unfold foc56
    linear_combination P.α * h57
  rw [key]
  apply mul_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg hγ (by linarith)
  · have : 0 < (1 - P.α) * (1 + P.lam) := mul_pos (by linarith) (by linarith)
    have : 0 < P.α * P.lam := mul_pos hα0 hlam
    linarith

end BIInsurance.Screening.FocCmp

open BIInsurance.Screening in
theorem solution (P : Params) (hS : P.Standing) (s : ℝ) (_hs : s ∈ Set.Icc 0 P.sbar)
    (h57 : foc57 P s = 0) :
    foc56 P s < 0 :=
  BIInsurance.Screening.FocCmp.main P hS s h57
