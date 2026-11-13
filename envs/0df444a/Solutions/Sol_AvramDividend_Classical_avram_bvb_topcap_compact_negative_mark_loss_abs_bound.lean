-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_compact_negative_mark_loss_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:01:56.306186+00:00
-- url     : https://prove2.me/submissions/4f188d85-88fb-41bc-bc01-771a4e037198

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ b z : ℝ, 0 ≤ b → b ≤ B → z < 0 → |w (b + z) - w b| ≤ K := by
  have hsubset : Icc (0 : ℝ) B ⊆ Ici (0 : ℝ) := by
    intro y hy
    exact hy.1
  have hcont : ContinuousOn w (Icc (0 : ℝ) B) := hw.mono hsubset
  have hLower (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0 : ℝ) B)) :
      ∃ L : ℝ, 0 ≤ L ∧ ∀ y : ℝ, 0 ≤ y → y ≤ B → -L ≤ f y := by
    have hc : IsCompact (Set.image f (Icc (0 : ℝ) B)) :=
      isCompact_Icc.image_of_continuousOn hf
    obtain ⟨R, hR⟩ := hc.isBounded.bddBelow
    refine ⟨max 0 (-R), le_max_left _ _, ?_⟩
    intro y hy0 hyB
    have hy : R ≤ f y := hR ⟨y, ⟨hy0, hyB⟩, rfl⟩
    have hbound : -max 0 (-R) ≤ R := by
      have hh : -R ≤ max 0 (-R) := le_max_right _ _
      linarith
    exact hbound.trans hy
  obtain ⟨L, hL0, hL⟩ := hLower w hcont
  obtain ⟨U, hU0, hU⟩ := hLower (fun y : ℝ => -w y) hcont.neg
  let K : ℝ := L + U
  have hK0 : 0 ≤ K := add_nonneg hL0 hU0
  have hBound (y : ℝ) (hy0 : 0 ≤ y) (hyB : y ≤ B) : |w y| ≤ K := by
    have hlo := hL y hy0 hyB
    have hhi := hU y hy0 hyB
    exact abs_le.mpr ⟨by dsimp [K]; linarith, by dsimp [K]; linarith⟩
  refine ⟨K + K, add_nonneg hK0 hK0, ?_⟩
  intro b z hb0 hbB hz
  have hb := hBound b hb0 hbB
  by_cases hneg : b + z < 0
  · rw [hw_neg (b + z) hneg]
    simpa [abs_neg] using le_trans hb (by linarith : K ≤ K + K)
  · have hbz0 : 0 ≤ b + z := le_of_not_gt hneg
    have hbzB : b + z ≤ B := by linarith
    have hbz := hBound (b + z) hbz0 hbzB
    calc
      |w (b + z) - w b| ≤ |w (b + z)| + |w b| := by
        simpa [sub_eq_add_neg] using (abs_add_le (w (b + z)) (-w b))
      _ ≤ K + K := add_le_add hbz hb
