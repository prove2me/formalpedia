-- Prove2me | solution 1 for Formalism.CountingSumsFrames.binomial_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:49.223387+00:00
-- url     : https://prove2.me/submissions/41deafe2-3442-400e-8b96-4cfd16920d79

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_pos_real
import Theorems.Thm_Formalism_CountingSumsFrames_binomSeries_gen
import Theorems.Thm_Formalism_CountingSumsFrames_tail_q_bound

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
theorem _root_.solution : BinomTail := by
  intro k' be J La b' hk hb hLa hJ hwin
  have hk2 : 2 ≤ k' := by omega
  have hk5 : (5 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have hs := binomSeries_gen k' (be + J) hk2
  have pJ := dimPol_pos_real k' (be + J)
  have pb := dimPol_pos_real k' be
  have hs2 := hs.mul_left ((dimPol k' be : ℝ) / dimPol k' (be + J))
  have hfun : (fun j : ℕ => (dimPol k' be : ℝ) / dimPol k' (be + J)
      * ((dimPol k' (be + J) : ℝ) / dimPol k' (be + J + j)))
      = fun j => (dimPol k' be : ℝ) / dimPol k' (be + J + j) := by
    funext j; have := dimPol_pos_real k' (be + J + j); field_simp
  rw [hfun] at hs2
  rw [hs2.tsum_eq]
  have hq := tail_q_bound k' be b' (by omega) hb J (by linarith)
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have hexp : Real.exp (-((k' : ℝ) - 1) * J / (2 * b')) ≤ Real.exp (-La / 3) := by
    apply Real.exp_le_exp.mpr
    have h1 : La * b' ≤ J * ((k' : ℝ) + 1) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < k' + 1)).mp hJ; linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hJ0 (sub_nonneg.mpr hk5)]
  push_cast
  calc (dimPol k' be : ℝ) / dimPol k' (be + J) * (((be : ℝ) + J + k') / ((k' : ℝ) - 1))
      = ((dimPol k' be : ℝ) * ((be : ℝ) + J + k') / dimPol k' (be + J)) / ((k' : ℝ) - 1) := by ring
    _ ≤ (((be : ℝ) + k') * Real.exp (-((k' : ℝ) - 1) * J / (2 * b'))) / ((k' : ℝ) - 1) :=
        div_le_div_of_nonneg_right hq hk1.le
    _ ≤ (((be : ℝ) + k') * Real.exp (-La / 3)) / ((k' : ℝ) - 1) := by
        gcongr
    _ = Real.exp (-La / 3) * (((be : ℝ) + k') / ((k' : ℝ) - 1)) := by ring
end Formalism.CountingSumsFrames
