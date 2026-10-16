-- Prove2me | solution 1 for ChenSimchiLevi.General.lemma_5_d
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T04:24:46.647779+00:00
-- url     : https://prove2.me/submissions/02766524-1a1c-4326-b173-865655736482

import Mathlib
import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

open ChenSimchiLevi.General Filter in
theorem solution (k : ℝ) (g : ℝ → ℝ) (hk : 0 ≤ k)
    (hg : SymKConvex k g) (hcont : Continuous g)
    (h₁ : Tendsto g atTop atTop) (h₂ : Tendsto g atBot atTop) :
    ∃ s S : ℝ, s ≤ S ∧ (∀ y, g S ≤ g y) ∧
      IsLeast {x | g x = g S + k} s ∧
      (∀ y < s, g s < g y) ∧
      ∀ y z, (s + S) / 2 ≤ y → y ≤ z → g y ≤ g z + k := by
  -- a global minimizer
  have hco : Tendsto g (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]; exact h₂.sup h₁
  obtain ⟨S, hS⟩ := hcont.exists_forall_le hco
  -- far-left strict bound
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ b ≤ a, g S + k < g b :=
    eventually_atBot.mp (h₂.eventually (eventually_gt_atTop (g S + k)))
  -- a point left of S at level gS + k
  have hx0 : ∃ x0 ≤ S, g x0 = g S + k := by
    have hab : min a S ≤ S := min_le_right _ _
    have h1 : g S + k < g (min a S) := ha _ (min_le_left _ _)
    have := intermediate_value_Icc' hab hcont.continuousOn
      (show g S + k ∈ Set.Icc (g S) (g (min a S)) from ⟨by linarith, h1.le⟩)
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨x, hx.2, hxe⟩
  obtain ⟨x0, hx0S, hx0e⟩ := hx0
  -- least point of the level set
  have hleast : ∃ s, IsLeast {x | g x = g S + k} s := by
    have hcpt : IsCompact ({x | g x = g S + k} ∩ Set.Icc (min a x0) x0) :=
      isCompact_Icc.inter_left (isClosed_eq hcont continuous_const)
    have hne : ({x | g x = g S + k} ∩ Set.Icc (min a x0) x0).Nonempty :=
      ⟨x0, hx0e, min_le_right _ _, le_refl _⟩
    obtain ⟨s, hs⟩ := hcpt.exists_isLeast hne
    refine ⟨s, hs.1.1, fun x hx => ?_⟩
    by_cases hxx : x ≤ x0
    · have hmin : min a x0 ≤ x := by
        by_contra hlt
        push_neg at hlt
        have := ha x ((lt_of_lt_of_le hlt (min_le_left _ _)).le)
        rw [hx] at this
        exact lt_irrefl _ this
      exact hs.2 ⟨hx, hmin, hxx⟩
    · push_neg at hxx
      exact le_trans (hs.2 ⟨hx0e, min_le_right _ _, le_refl _⟩) hxx.le
  obtain ⟨s, hs⟩ := hleast
  have hsx0 : s ≤ x0 := hs.2 hx0e
  have hsS : s ≤ S := le_trans hsx0 hx0S
  have hgs : g s = g S + k := hs.1
  refine ⟨s, S, hsS, hS, hs, ?_, ?_⟩
  · intro y hy
    by_contra hnot
    push_neg at hnot
    have hne : g y ≠ g S + k := fun h => absurd (hs.2 h) (not_le.mpr hy)
    have hlt : g y < g S + k := lt_of_le_of_ne (by rw [← hgs]; exact hnot) hne
    have hab : min a y ≤ y := min_le_right _ _
    have h1 : g S + k < g (min a y) := ha _ (min_le_left _ _)
    obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc' hab hcont.continuousOn
      (show g S + k ∈ Set.Icc (g y) (g (min a y)) from ⟨hlt.le, h1.le⟩)
    have := hs.2 hxe
    linarith [hx.2]
  · intro y z hy hyz
    by_cases hyS : S ≤ y
    · -- y between S and z
      rcases eq_or_lt_of_le hyS with h | h
      · rw [← h]; linarith [hS z]
      · have hSz : S < z := lt_of_lt_of_le h hyz
        set l : ℝ := (y - S) / (z - S) with hl
        have hzS : 0 < z - S := by linarith
        have hl0 : 0 ≤ l := div_nonneg (by linarith) hzS.le
        have hl1 : l ≤ 1 := by rw [hl, div_le_one hzS]; linarith
        have hyeq : y = (1 - l) * S + l * z := by
          rw [hl]; field_simp; ring
        have := hg S z l ⟨hl0, hl1⟩
        rw [← hyeq] at this
        have hm : max l (1 - l) ≤ 1 := max_le hl1 (by linarith)
        have hgS := hS z
        have h1l : 0 ≤ 1 - l := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hm hk, mul_le_mul_of_nonneg_left hgS h1l]
    · push_neg at hyS
      -- y in [(s+S)/2, S)
      have hsy : s < y := by linarith
      have hSs : 0 < S - s := by linarith
      set l : ℝ := (y - s) / (S - s) with hl
      have hl0 : 0 ≤ l := div_nonneg (by linarith) hSs.le
      have hl1 : l ≤ 1 := by rw [hl, div_le_one hSs]; linarith
      have hlh : 1 / 2 ≤ l := by
        rw [hl, le_div_iff₀ hSs]; linarith
      have hyeq : y = (1 - l) * s + l * S := by
        rw [hl]; field_simp; ring
      have := hg s S l ⟨hl0, hl1⟩
      rw [← hyeq, hgs] at this
      have hmax : max l (1 - l) = l := max_eq_left (by linarith)
      rw [hmax] at this
      nlinarith [hS z, this]
