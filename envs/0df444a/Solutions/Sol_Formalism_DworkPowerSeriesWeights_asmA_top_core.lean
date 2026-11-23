-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmA_top_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:58.733543+00:00
-- url     : https://prove2.me/submissions/e126852b-288b-41bb-a2b9-6cb003a5d21c

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) (hl : 2 ≤ l) (A : ℝ) (cap h : ℕ → ℝ)
    (hcap : ∀ j, 0 ≤ cap j) (hh : ∀ e, 0 ≤ h e) (hsum : Summable h) (R : Finset ℕ) (T : ℕ)
    (hT : A / (l : ℝ) ^ T ≤ h T) (hR : ∀ j ∈ R, j < T → cap j ≤ h j) :
    A * ((l : ℝ) ^ T)⁻¹ + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0 ≤
      ∑' e, h e := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hterm : ∀ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0 ≤
      if j < T then h j else 0 := by
    intro j hj
    split_ifs with hjT
    · have hpos : 0 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹ := by positivity
      calc cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0 ≤ cap j * 1 :=
            mul_le_mul_of_nonneg_left (max_le (by linarith) zero_le_one) (hcap j)
        _ = cap j := mul_one _
        _ ≤ h j := hR j hj hjT
    · have h1 : 1 ≤ (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ hl1 (not_lt.mp hjT)
      rw [max_eq_right (by linarith), mul_zero]
  have hsumR : ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0 ≤
      ∑ j ∈ Finset.range T, h j := by
    calc _ ≤ ∑ j ∈ R, (if j < T then h j else 0) := Finset.sum_le_sum hterm
      _ = ∑ j ∈ R.filter (· < T), h j := (Finset.sum_filter _ _).symm
      _ ≤ ∑ j ∈ Finset.range T, h j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_filter] at hj
          exact Finset.mem_range.mpr hj.2
        · intro i _ _
          exact hh i
  have hA : A * ((l : ℝ) ^ T)⁻¹ ≤ h T := by rw [← div_eq_mul_inv]; exact hT
  calc A * ((l : ℝ) ^ T)⁻¹ + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ((l : ℝ) ^ T)⁻¹) 0
      ≤ ∑ j ∈ Finset.range T, h j + h T := by linarith
    _ = ∑ j ∈ Finset.range (T + 1), h j := (Finset.sum_range_succ _ _).symm
    _ ≤ ∑' e, h e := Summable.sum_le_tsum _ (fun i _ => hh i) hsum
end Formalism.DworkPowerSeriesWeights
