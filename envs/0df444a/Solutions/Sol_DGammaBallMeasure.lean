-- Prove2me | solution 1 for DGammaBallMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:00.606196+00:00
-- url     : https://prove2.me/submissions/3dba5a55-5f95-4339-8eef-f9eec0308359

import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_DGammaBallMeasure

set_option autoImplicit false
open MeasureTheory Set ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (s ρ : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) γ.len) (hρ : 0 < ρ) :
    volume { t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < ρ } ≤ ENNReal.ofReal (2 * ρ) := by
-- BODY
  obtain ⟨hs0, hsl⟩ := hs
  by_cases hc : IsClosedCurve γ
  · -- Case 2: `γ` is closed, so `dGamma γ s t = min |s - t| (γ.len - |s - t|)`.
    -- The sublevel set splits as `S₁ ∪ S₂` with `S₂ ⊆ S₂ₐ ∪ S₂ᵦ`, and each piece is caught
    -- inside an explicit closed interval.
    have hsub : { t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < ρ } ⊆
        (Set.Icc (max 0 (s - ρ)) (min γ.len (s + ρ)) ∪
            Set.Icc (0 : ℝ) (max 0 (s + ρ - γ.len))) ∪
          Set.Icc (min γ.len (s + γ.len - ρ)) γ.len := by
      rintro t ⟨⟨ht0, htl⟩, hlt⟩
      simp only [dGamma, if_pos hc, min_lt_iff] at hlt
      rcases hlt with h | h
      · -- `|s - t| < ρ`: `t` lies in `[0, γ.len] ∩ (s - ρ, s + ρ)`.
        rw [abs_lt] at h
        exact Or.inl (Or.inl ⟨max_le ht0 (by linarith [h.1]), le_min htl (by linarith [h.2])⟩)
      · -- `|s - t| > γ.len - ρ`: `t` is near one of the two endpoints of `[0, γ.len]`.
        have h' : γ.len - ρ < |s - t| := by linarith
        rw [lt_abs] at h'
        rcases h' with h' | h'
        · exact Or.inl (Or.inr ⟨ht0, (by linarith : t ≤ s + ρ - γ.len).trans (le_max_right _ _)⟩)
        · exact Or.inr ⟨(min_le_right _ _).trans (by linarith), htl⟩
    -- The three interval lengths are nonnegative and sum to exactly `2ρ`.
    have hM1 : min γ.len (s + ρ) = (s + ρ) - max 0 (s + ρ - γ.len) := by
      rcases le_total γ.len (s + ρ) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    have hM3 : min γ.len (s + γ.len - ρ) = (s + γ.len - ρ) - max 0 (s - ρ) := by
      rcases le_total γ.len (s + γ.len - ρ) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    have hM2 : max 0 (s - ρ) = (s - ρ) + max 0 (ρ - s) := by
      rcases le_total 0 (s - ρ) with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    have hA : (0 : ℝ) ≤ min γ.len (s + ρ) - max 0 (s - ρ) := by
      have h1 : max 0 (s - ρ) ≤ s := max_le hs0 (by linarith)
      have h2 : s ≤ min γ.len (s + ρ) := le_min hsl (by linarith)
      linarith
    have hB : (0 : ℝ) ≤ max 0 (s + ρ - γ.len) - 0 := by
      have := le_max_left (0 : ℝ) (s + ρ - γ.len); linarith
    have hC : (0 : ℝ) ≤ γ.len - min γ.len (s + γ.len - ρ) := by
      have := min_le_left γ.len (s + γ.len - ρ); linarith
    have hsum : (min γ.len (s + ρ) - max 0 (s - ρ)) + (max 0 (s + ρ - γ.len) - 0)
        + (γ.len - min γ.len (s + γ.len - ρ)) = 2 * ρ := by
      rw [hM1, hM3, hM2]; ring
    calc volume { t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < ρ }
        ≤ volume ((Set.Icc (max 0 (s - ρ)) (min γ.len (s + ρ)) ∪
            Set.Icc (0 : ℝ) (max 0 (s + ρ - γ.len))) ∪
            Set.Icc (min γ.len (s + γ.len - ρ)) γ.len) := measure_mono hsub
      _ ≤ volume (Set.Icc (max 0 (s - ρ)) (min γ.len (s + ρ)) ∪
            Set.Icc (0 : ℝ) (max 0 (s + ρ - γ.len))) +
            volume (Set.Icc (min γ.len (s + γ.len - ρ)) γ.len) := measure_union_le _ _
      _ ≤ volume (Set.Icc (max 0 (s - ρ)) (min γ.len (s + ρ))) +
            volume (Set.Icc (0 : ℝ) (max 0 (s + ρ - γ.len))) +
            volume (Set.Icc (min γ.len (s + γ.len - ρ)) γ.len) :=
          add_le_add (measure_union_le _ _) le_rfl
      _ = ENNReal.ofReal (2 * ρ) := by
          rw [Real.volume_Icc, Real.volume_Icc, Real.volume_Icc,
            ← ENNReal.ofReal_add hA hB, ← ENNReal.ofReal_add (by linarith) hC, hsum]
  · -- Case 1: `γ` is not closed, so `dGamma γ s t = |s - t|` and the set sits inside
    -- the open interval `(s - ρ, s + ρ)` of length `2ρ`.
    have hsub : { t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < ρ } ⊆
        Set.Ioo (s - ρ) (s + ρ) := by
      rintro t ⟨-, hlt⟩
      simp only [dGamma, if_neg hc, abs_lt] at hlt
      exact ⟨by linarith [hlt.2], by linarith [hlt.1]⟩
    calc volume { t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < ρ }
        ≤ volume (Set.Ioo (s - ρ) (s + ρ)) := measure_mono hsub
      _ = ENNReal.ofReal (2 * ρ) := by rw [Real.volume_Ioo]; congr 1; ring
