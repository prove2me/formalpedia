-- Prove2me | solution 1 for Formalism.CohomologicalDescent.gatedPrimeSum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:34.139288+00:00
-- url     : https://prove2.me/submissions/57693e21-8c6b-40b1-a940-c30d44881765

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Theorems.Thm_Formalism_CohomologicalDescent_sums_harmonic_real
import Theorems.Thm_Formalism_CohomologicalDescent_leastCongruentPos_mem_le
import Theorems.Thm_Formalism_CohomologicalDescent_sums_le_of_gate
import Theorems.Thm_Formalism_CohomologicalDescent_sums_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution : GatedSum := by
  intro D h L A k P hD hDh hA hk hh hL hP
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast le_trans hD hDh
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  have step1 : ∑ l ∈ P, (if ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ) then
        min k (A / (d0 l (D : ℤ) : ℝ)) else 0) * Real.log (l : ℝ) ≤
      ∑ l ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
        (A / (d0 l (D : ℤ) : ℝ)) * Real.log (h : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    obtain ⟨hlp, _⟩ := hP l hl
    split_ifs with hgl
    · have hsub := sums_le_of_gate l D hD hgl
      have hlh : (l : ℝ) ≤ (h : ℝ) := by
        have h1 : (l : ℤ) ≤ (h : ℤ) := by
          have : (D : ℤ) ≤ (h : ℤ) := by exact_mod_cast hDh
          have : (0 : ℤ) ≤ ((d0 l (D : ℤ) : ℕ) : ℤ) := by positivity
          linarith
        exact_mod_cast h1
      have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlp.one_lt.le
      exact mul_le_mul (min_le_right _ _) (Real.log_le_log (by linarith) hlh)
        (Real.log_nonneg hl1) (div_nonneg hA (Nat.cast_nonneg _))
    · simp
  have hinj : ∀ x ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
      ∀ y ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
      d0 x (D : ℤ) = d0 y (D : ℤ) → x = y := by
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.1 hx
    have hy' := Finset.mem_filter.1 hy
    obtain ⟨hxp, hLx⟩ := hP x hx'.1
    obtain ⟨hyp, hLy⟩ := hP y hy'.1
    exact sums_inj D h L hD hDh hh hL x y hxp hyp hLx hLy hx'.2 hxy
  have step2 : ∑ l ∈ P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)),
        (A / (d0 l (D : ℤ) : ℝ)) * Real.log (h : ℝ) =
      ∑ x ∈ (P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))).image
        (fun l => d0 l (D : ℤ)), (A / (x : ℝ)) * Real.log (h : ℝ) := by
    rw [Finset.sum_image hinj]
  have hsub : (P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))).image
      (fun l => d0 l (D : ℤ)) ⊆ Finset.Icc 1 h := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, _, h2⟩ := leastCongruentPos_mem_le l D hD
    exact Finset.mem_Icc.2 ⟨h1, le_trans h2 hDh⟩
  have step3 : ∑ x ∈ (P.filter (fun l => ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ))).image
        (fun l => d0 l (D : ℤ)), (A / (x : ℝ)) * Real.log (h : ℝ) ≤
      ∑ x ∈ Finset.Icc 1 h, (A / (x : ℝ)) * Real.log (h : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => mul_nonneg (div_nonneg hA (Nat.cast_nonneg _)) hlogh)
  have step4 : ∑ x ∈ Finset.Icc 1 h, (A / (x : ℝ)) * Real.log (h : ℝ) =
      A * Real.log (h : ℝ) * ∑ x ∈ Finset.Icc 1 h, (1 : ℝ) / (x : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hH := sums_harmonic_real h
  have hAl : 0 ≤ A * Real.log (h : ℝ) := mul_nonneg hA hlogh
  refine le_trans step1 ?_
  rw [step2]
  refine le_trans step3 ?_
  rw [step4]
  calc A * Real.log (h : ℝ) * ∑ x ∈ Finset.Icc 1 h, (1 : ℝ) / (x : ℝ)
      ≤ A * Real.log (h : ℝ) * (1 + Real.log h) := mul_le_mul_of_nonneg_left hH hAl
    _ = A * (1 + Real.log (h : ℝ)) * Real.log (h : ℝ) := by ring
end Formalism.CohomologicalDescent
