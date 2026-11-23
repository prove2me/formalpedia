-- Prove2me | solution 1 for Formalism.CountingSumsFrames.digit_class_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:38.679118+00:00
-- url     : https://prove2.me/submissions/43c93125-48d9-4196-a211-8ec20f9ee210

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity
import Theorems.Thm_Formalism_CountingSumsFrames_digit_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : DigitClassSize := by
  intro m P g e hP hg he
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by positivity
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  set t : ℝ := ((m : ℝ) + 1) * P / g with ht_def
  have ht : 0 ≤ t := by positivity
  have hgle : (g : ℝ) ≤ P * ((e : ℝ) + (m + 1)) := by
    have : (g : ℝ) / P ≤ (e : ℝ) + (m + 1) := by linarith
    rw [div_le_iff₀ hPpos] at this
    linarith
  have htg : t * g = ((m : ℝ) + 1) * P := by
    rw [ht_def]; field_simp
  have hkey : ∀ j : ℕ, (1 - t) * ((g : ℝ) + j + 1) ≤ (P : ℝ) * ((e : ℝ) + j + 1) := by
    intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have htj : 0 ≤ t * ((j : ℝ) + 1) := by positivity
    nlinarith
  have main := digit_step P g e t ht hkey m
  have hdim : ∀ d, (dimPol m d : ℝ) = ((d + m).choose m : ℝ) := fun d => rfl
  rw [hdim, hdim]
  have hfac : 1 - ((m : ℝ) + 1) ^ 2 * P / g ≤ 1 - (m : ℝ) * t := by
    have : ((m : ℝ) + 1) ^ 2 * P / g = ((m : ℝ) + 1) * t := by
      rw [ht_def]; ring
    rw [this]
    nlinarith
  calc (1 - ((m : ℝ) + 1) ^ 2 * P / g) * ((g + m).choose m : ℝ)
      ≤ (1 - (m : ℝ) * t) * ((g + m).choose m : ℝ) :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ ≤ (P : ℝ) ^ m * ((e + m).choose m : ℝ) := main
end Formalism.CountingSumsFrames
