-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB44_original_BV_derivative_maximum_absorbs_small_mark_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:50:56.290723+00:00
-- url     : https://prove2.me/submissions/80f54f4e-aa2b-4be0-8470-b02300f7306f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem solution
    (d η A B ε c : ℝ) (hd : η < d)
    (hε : 0 < ε) (hc : ε < c)
    (w : ℝ → ℝ)
    (hLocal : ∀ t ∈ Icc (ε / 2) ε, deriv w t ≤ B)
    (hMax : ∀ b ∈ Ioo ε c,
      ∃ s ∈ Icc (ε / 2) b,
        ∀ t ∈ Icc (ε / 2) b, deriv w t ≤ deriv w s)
    (hEnv : ∀ b ∈ Ioo ε c,
      ∀ s ∈ Icc ε b,
      ∀ M : ℝ,
      (∀ t ∈ Icc (ε / 2) b, deriv w t ≤ M) →
      d * deriv w s ≤ A + η * M) :
    ∀ t ∈ Ico (ε / 2) c,
      deriv w t ≤ max B (A / (d - η)) := by
  intro t ht
  by_cases hte : t ≤ ε
  · exact (hLocal t ⟨ht.1, hte⟩).trans (le_max_left _ _)
  · have htε : ε < t := lt_of_not_ge hte
    let b : ℝ := (t + c) / 2
    have hbe : ε < b := by dsimp [b]; linarith
    have hbc : b < c := by dsimp [b]; linarith [ht.2]
    have htb : t ≤ b := by dsimp [b]; linarith [ht.2]
    obtain ⟨s, hs, hsMax⟩ := hMax b ⟨hbe, hbc⟩
    have htBand : t ∈ Icc (ε / 2) b := ⟨ht.1, htb⟩
    have htle : deriv w t ≤ deriv w s := hsMax t htBand
    by_cases hse : s ≤ ε
    · have hsLocal : s ∈ Icc (ε / 2) ε := ⟨hs.1, hse⟩
      exact (htle.trans (hLocal s hsLocal)).trans (le_max_left _ _)
    · have hsLower : ε ≤ s := le_of_lt (lt_of_not_ge hse)
      have hsInner : s ∈ Icc ε b := ⟨hsLower, hs.2⟩
      have hHJB := hEnv b ⟨hbe, hbc⟩ s hsInner (deriv w s) hsMax
      have hD : 0 < d - η := sub_pos.mpr hd
      have hsBound : deriv w s ≤ A / (d - η) := by
        apply (le_div_iff₀ hD).2
        nlinarith
      exact (htle.trans hsBound).trans (le_max_right _ _)
