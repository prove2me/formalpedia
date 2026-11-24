-- Prove2me | solution 1 for FairSelling.FeigeNorkin.feigeNorkin_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:42.817296+00:00
-- url     : https://prove2.me/submissions/9fdf8903-abf1-4f8e-8b9b-dd7d086c3eca

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
import Theorems.Thm_FairSelling_FeigeNorkin_feigeNorkin_disjoint

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
namespace FairSelling.FeigeNorkin
theorem _root_.solution (A : Fin 3 → Finset (Fin 8))
    (hA : ∀ i k, i ≠ k → Disjoint (A i) (A k)) :
    (∑ g ∈ A 0, (fnR g : ℝ)) ≤ (11/12) * 36 ∨
    (∑ g ∈ A 1, (fnC g : ℝ)) ≤ (11/12) * 36 ∨
    (∑ g ∈ A 2, (fnU g : ℝ)) ≤ (11/12) * 36 := by
  obtain ⟨i, hi⟩ := feigeNorkin_disjoint A hA
  have hcast : ∀ (s : Finset (Fin 8)) (w : Fin 8 → ℕ), (∑ g ∈ s, w g) ≤ 33 →
      (∑ g ∈ s, (w g : ℝ)) ≤ (11/12) * 36 := by
    intro s w h
    have : (∑ g ∈ s, (w g : ℝ)) ≤ (33 : ℕ) := by
      rw [← Nat.cast_sum]; exact_mod_cast h
    norm_num at this ⊢
    linarith
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi3 with rfl | rfl | rfl
  · exact Or.inl (hcast _ _ (by simpa [fnW] using hi))
  · exact Or.inr (Or.inl (hcast _ _ (by simpa [fnW] using hi)))
  · exact Or.inr (Or.inr (hcast _ _ (by simpa [fnW] using hi)))
end FairSelling.FeigeNorkin
