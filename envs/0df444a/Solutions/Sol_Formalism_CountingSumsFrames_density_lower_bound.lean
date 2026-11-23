-- Prove2me | solution 1 for Formalism.CountingSumsFrames.density_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:11.069809+00:00
-- url     : https://prove2.me/submissions/473ed1be-c0a9-47c2-b5c0-71af82ca072c

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_pos_real
import Theorems.Thm_Formalism_CountingSumsFrames_binomial_ratio_bound
import Theorems.Thm_Formalism_CountingSumsFrames_binomSeries_gen
import Theorems.Thm_Formalism_CountingSumsFrames_binomial_tail_bound
import Theorems.Thm_Formalism_CountingSumsFrames_dimHar_ratio_ge

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
theorem _root_.solution : DensityLower := by
  intro k' al be La b' hk hal hb hLa hwin
  set J0 : ℝ := La * b' / (k' + 1) with hJ0
  set N : ℕ := ⌊J0⌋₊ + 1 with hN
  have hk2 : 2 ≤ k' := by omega
  have hk5 : (5 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have hal' : (0 : ℝ) < al := by exact_mod_cast hal
  have hJ00 : 0 ≤ J0 := by positivity
  have he0 : 0 ≤ 1 - Real.exp (-La / 3) := by
    have : Real.exp (-La / 3) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have pa := dimPol_pos_real k' al
  have pb := dimPol_pos_real k' be
  have hH0 : (0 : ℝ) ≤ dimHar k' al be := by positivity
  set h : ℝ := (dimHar k' al be : ℝ) / ((dimPol k' al : ℝ) * dimPol k' be) with hh
  have hh0 : 0 ≤ h := by positivity
  have hhS := dimHar_ratio_ge k' al be hk2 hal
  set S : ℝ := ((be : ℝ) + k') / ((k' : ℝ) - 1) with hS
  set f : ℕ → ℝ := fun j => (dimPol k' be : ℝ) / dimPol k' (be + j) with hf
  have hser : HasSum f S := binomSeries_gen k' be hk2
  have hNJ : J0 ≤ (N : ℝ) := by rw [hN]; push_cast; exact (Nat.lt_floor_add_one J0).le
  have htail := binomial_tail_bound k' be N La b' hk hb hLa hNJ hwin
  have hsplit := hser.summable.sum_add_tsum_nat_add N
  have htail' : ∑' i, f (i + N) = ∑' j : ℕ, (dimPol k' be : ℝ) / dimPol k' (be + N + j) := by
    congr 1; funext i; simp only [hf]; rw [show be + (i + N) = be + N + i by omega]
  rw [hser.tsum_eq, htail'] at hsplit
  have hpart : S * (1 - Real.exp (-La / 3)) ≤ ∑ j ∈ range N, f j := by
    have : Real.exp (-La / 3) * S = S * Real.exp (-La / 3) := by ring
    nlinarith [htail]
  by_cases ha : 1 - (k' : ℝ) * J0 / al ≤ 0
  · have : (0 : ℝ) ≤ ∑ j ∈ range N,
        (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j)) := by
      apply Finset.sum_nonneg; intro j _
      have := dimPol_pos_real k' (al + j); have := dimPol_pos_real k' (be + j); positivity
    nlinarith [mul_nonneg (neg_nonneg.mpr ha) he0]
  · rw [not_le] at ha
    set a := 1 - (k' : ℝ) * J0 / al with hadef
    have hterm : ∀ j ∈ range N, h * a * f j
        ≤ (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j)) := by
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      have hjJ : (j : ℝ) ≤ J0 := by
        have : j ≤ ⌊J0⌋₊ := by omega
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le hJ00)
      have hr := binomial_ratio_bound k' al j hal
      have hra : a ≤ (dimPol k' al : ℝ) / dimPol k' (al + j) := by
        refine le_trans ?_ hr
        have : (k' : ℝ) * j / al ≤ (k' : ℝ) * J0 / al := by gcongr
        linarith
      have p1 := dimPol_pos_real k' (al + j)
      have p2 := dimPol_pos_real k' (be + j)
      have heq : (dimHar k' al be : ℝ) / ((dimPol k' (al + j) : ℝ) * dimPol k' (be + j))
          = h * ((dimPol k' al : ℝ) / dimPol k' (al + j)) * f j := by
        simp only [hh, hf]; field_simp
      rw [heq]
      have hf0 : 0 ≤ f j := by simp only [hf]; positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hra hh0) hf0
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have h1 : h * a * (S * (1 - Real.exp (-La / 3))) ≤ h * a * ∑ j ∈ range N, f j :=
      mul_le_mul_of_nonneg_left hpart (by positivity)
    have h2 : a * (1 - Real.exp (-La / 3)) ≤ h * a * (S * (1 - Real.exp (-La / 3))) := by
      have e : h * a * (S * (1 - Real.exp (-La / 3))) = (h * S) * (a * (1 - Real.exp (-La / 3))) := by
        ring
      rw [e]
      have hae : 0 ≤ a * (1 - Real.exp (-La / 3)) := mul_nonneg ha.le he0
      nlinarith
    linarith
end Formalism.CountingSumsFrames
