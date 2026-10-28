-- Prove2me | solution 1 for DealerDissem.RankFree.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:29:55.068265+00:00
-- url     : https://prove2.me/submissions/eda89989-c77d-4200-8b75-fa6cb15cb745

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

open DealerDissem.RankFree in
theorem solution (P : Params) (f : ℝ → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_lip : ∀ x x', 0 ≤ x → 0 ≤ x' → |f x - f x'| ≤ P.q * |x - x'|)
    (p v y ω : ℝ) (hωpv : ω ≤ p * v) (hωy : ω ≤ y) :
    min (p * v) y + f (p * v - ω) ≤ p * v + f (y - ω) := by
  rcases le_total y (p * v) with h | h
  · rw [min_eq_right h]
    have hl := hf_lip (p * v - ω) (y - ω) (by linarith) (by linarith)
    have e : |p * v - ω - (y - ω)| = p * v - y := by
      rw [abs_of_nonneg (by linarith)]; ring
    rw [e] at hl
    have h1 := (abs_le.mp hl).2
    have hq1 := P.hq1
    have hq0 := P.hq0
    nlinarith
  · rw [min_eq_left h]
    have := hf_mono (show (0:ℝ) ≤ p * v - ω by linarith : p * v - ω ∈ Set.Ici (0:ℝ))
      (show (0:ℝ) ≤ y - ω by linarith : y - ω ∈ Set.Ici (0:ℝ)) (by linarith)
    linarith
