-- Prove2me | solution 1 for Formalism.CountingSumsFrames.geom_sum_filter_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:41.592854+00:00
-- url     : https://prove2.me/submissions/f364c198-cb7a-4863-b007-edbf7ccbb6aa

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {s : ℕ} (i : Fin s) (q : ℝ) (hq0 : 0 ≤ q) :
    (1 - q) * ∑ l ∈ univ.filter (fun l : Fin s => l ≤ i), q ^ ((i:ℕ) - (l:ℕ)) ≤ 1 ∨ 1 < q := by
  rcases lt_or_ge 1 q with hq1 | hq1
  · exact Or.inr hq1
  left
  have h1 : ∑ l ∈ univ.filter (fun l : Fin s => l ≤ i), q ^ ((i:ℕ) - (l:ℕ))
      = ∑ e ∈ (univ.filter (fun l : Fin s => l ≤ i)).image (fun l : Fin s => (i:ℕ) - (l:ℕ)), q ^ e := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    have hx' : (x:ℕ) ≤ i := (mem_filter.1 hx).2
    have hy' : (y:ℕ) ≤ i := (mem_filter.1 hy).2
    apply Fin.ext
    simp only at hxy
    omega
  have h2 : (univ.filter (fun l : Fin s => l ≤ i)).image (fun l : Fin s => (i:ℕ) - (l:ℕ)) ⊆ range ((i:ℕ)+1) := by
    intro e he
    simp only [mem_image, mem_filter, mem_univ, true_and] at he
    obtain ⟨l, hl, rfl⟩ := he
    simp only [mem_range]; omega
  have h3 : (1 - q) * ∑ e ∈ range ((i:ℕ)+1), q^e ≤ 1 := by
    rw [mul_neg_geom_sum]
    have hpow : 0 ≤ q ^ ((i:ℕ)+1) := by positivity
    linarith
  rw [h1]
  exact (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg h2 (fun _ _ _ => by positivity))
    (by linarith)).trans h3
end Formalism.CountingSumsFrames
