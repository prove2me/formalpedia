-- Prove2me | solution 1 for Formalism.CountingSumsFrames.binomial_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:51.600635+00:00
-- url     : https://prove2.me/submissions/ef127db5-cc77-421b-81df-c363314627ae

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_pos_real
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_succ_eq_real

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
open Finset Filter Topology
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : BinomRatio := by
  intro k' al j hal
  have hal' : (0 : ℝ) < al := by exact_mod_cast hal
  induction j with
  | zero => simp [div_self (dimPol_pos_real k' al).ne']
  | succ j ih =>
    have p0 := dimPol_pos_real k' (al + j)
    have pa := dimPol_pos_real k' al
    have hrec := dimPol_succ_eq_real k' (al + j)
    rw [show al + (j + 1) = al + j + 1 by omega, hrec]
    push_cast at ih ⊢
    set r : ℝ := (dimPol k' al : ℝ) / dimPol k' (al + j) with hr
    have hr0 : 0 ≤ r := by positivity
    have hkey : (dimPol k' al : ℝ) / (dimPol k' (al + j) * ((al : ℝ) + j + 1 + k') / ((al : ℝ) + j + 1))
        = r * (((al : ℝ) + j + 1) / ((al : ℝ) + j + 1 + k')) := by
      rw [hr]; field_simp
    rw [hkey]
    set t : ℝ := ((al : ℝ) + j + 1) / ((al : ℝ) + j + 1 + k') with ht
    have hk0 : (0 : ℝ) ≤ k' := by positivity
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; linarith
    have h1t : 1 - t ≤ (k' : ℝ) / al := by
      have : 1 - t = (k' : ℝ) / ((al : ℝ) + j + 1 + k') := by rw [ht]; field_simp; ring
      rw [this]
      exact div_le_div_of_nonneg_left hk0 hal' (by linarith)
    have hexp : 1 - (k' : ℝ) * (j + 1) / al = (1 - (k' : ℝ) * j / al) - k' / al := by ring
    rw [hexp]
    by_cases ha : 1 - (k' : ℝ) * j / al ≤ 0
    · have : (0 : ℝ) ≤ k' / al := by positivity
      nlinarith [mul_nonneg hr0 ht0]
    · rw [not_le] at ha
      set a := 1 - (k' : ℝ) * j / al
      have ha1 : a ≤ 1 := by
        have : (0 : ℝ) ≤ k' * j / al := by positivity
        linarith
      have h2 : a * t ≤ r * t := mul_le_mul_of_nonneg_right ih ht0
      have h3 : a * (1 - t) ≤ 1 - t := by nlinarith
      nlinarith
end Formalism.CountingSumsFrames
