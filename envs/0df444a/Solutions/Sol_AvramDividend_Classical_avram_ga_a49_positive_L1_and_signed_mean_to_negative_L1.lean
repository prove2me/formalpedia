-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a49_positive_L1_and_signed_mean_to_negative_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:25:56.726225+00:00
-- url     : https://prove2.me/submissions/055bede0-3499-4a76-b95a-a25e23cdf0f0

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ)
    (hPos : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (f m ω) (0 : ℝ)) P ∧
      (∫ ω, max (f m ω) (0 : ℝ) ∂P) ≤ ε)
    (hSigned : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (f m) P ∧
      |(∫ ω, f m ω ∂P)| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (-f m ω) (0 : ℝ)) P ∧
      (∫ ω, max (-f m ω) (0 : ℝ) ∂P) ≤ ε := by
  intro ε hε
  have hh : 0 < ε / 2 := by linarith
  obtain ⟨kp, hp⟩ := hPos (ε / 2) hh
  obtain ⟨ks, hs⟩ := hSigned (ε / 2) hh
  refine ⟨max kp ks, ?_⟩
  intro m hm
  obtain ⟨hPI, hPBound⟩ :=
    hp m (le_trans (le_max_left kp ks) hm)
  obtain ⟨hBI, hBAbs⟩ :=
    hs m (le_trans (le_max_right kp ks) hm)
  have hId : (fun ω => max (-f m ω) (0 : ℝ)) =
      (fun ω => max (f m ω) (0 : ℝ) - f m ω) := by
    funext ω
    by_cases h : 0 ≤ f m ω
    · have hn : -f m ω ≤ 0 := neg_nonpos.mpr h
      simp [max_eq_left h, max_eq_right hn]
    · have hlt : f m ω < 0 := lt_of_not_ge h
      have hn : 0 ≤ -f m ω := neg_nonneg.mpr (le_of_lt hlt)
      simp [max_eq_right (le_of_lt hlt), max_eq_left hn]
  have hNI : Integrable (fun ω => max (-f m ω) (0 : ℝ)) P := by
    rw [hId]
    exact hPI.sub hBI
  have hIntegral : (∫ ω, max (-f m ω) (0 : ℝ) ∂P) =
      (∫ ω, max (f m ω) (0 : ℝ) ∂P) -
      (∫ ω, f m ω ∂P) := by
    rw [hId, integral_sub hPI hBI]
  have hLower : -(ε / 2) ≤ (∫ ω, f m ω ∂P) :=
    (abs_le.mp hBAbs).1
  exact ⟨hNI, by rw [hIntegral]; linarith⟩
