-- Prove2me | solution 1 for Disjunctive.Polarity.reverse_polar_scaled_stabilizes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:21:13.40902+00:00
-- url     : https://prove2.me/submissions/128422c5-e055-4a4f-8199-eb2df2f46e69

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Polars

open Disjunctive.Polarity

theorem solution {n : ℕ} (F : Set (Fin n → ℝ)) (α0 : ℝ) :
    ScaledPolar (ScaledPolar (ScaledPolar F α0) α0) α0 = ScaledPolar F α0 := by
  -- `ScaledPolar · α0` is antitone, and every set is contained in its double scaled polar
  have hanti : ∀ S T : Set (Fin n → ℝ), S ⊆ T → ScaledPolar T α0 ⊆ ScaledPolar S α0 := by
    intro S T hST y hy x hx
    exact hy x (hST hx)
  have hdouble : ∀ S : Set (Fin n → ℝ), S ⊆ ScaledPolar (ScaledPolar S α0) α0 := by
    intro S x hx z hz
    have h := hz x hx
    rw [dotProduct_comm]
    exact h
  apply Set.Subset.antisymm
  · exact hanti _ _ (hdouble F)
  · exact hdouble (ScaledPolar F α0)
