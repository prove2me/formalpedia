-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a46_positive_negative_L1_to_absolute
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:16:26.753945+00:00
-- url     : https://prove2.me/submissions/8401553f-1914-49ad-b49e-e754578bebcc

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
    (hNeg : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (-f m ω) (0 : ℝ)) P ∧
      (∫ ω, max (-f m ω) (0 : ℝ) ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |f m ω|) P ∧
      (∫ ω, |f m ω| ∂P) ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨kp, hp⟩ := hPos (ε / 2) hhalf
  obtain ⟨kn, hn⟩ := hNeg (ε / 2) hhalf
  refine ⟨max kp kn, ?_⟩
  intro m hm
  obtain ⟨hIp, hEp⟩ :=
    hp m (le_trans (le_max_left kp kn) hm)
  obtain ⟨hIn, hEn⟩ :=
    hn m (le_trans (le_max_right kp kn) hm)
  have hEq : (fun ω => |f m ω|) =
      (fun ω => max (f m ω) (0 : ℝ)) +
      (fun ω => max (-f m ω) (0 : ℝ)) := by
    funext ω
    by_cases h : 0 ≤ f m ω
    · have hn0 : -f m ω ≤ 0 := neg_nonpos.mpr h
      simp [max_eq_left h, max_eq_right hn0, abs_of_nonneg h]
    · have hlt : f m ω < 0 := lt_of_not_ge h
      have hp0 : 0 ≤ -f m ω := neg_nonneg.mpr (le_of_lt hlt)
      simp [max_eq_right (le_of_lt hlt), max_eq_left hp0, abs_of_neg hlt]
  have hI : Integrable (fun ω => |f m ω|) P := by
    rw [hEq]
    exact hIp.add hIn
  have hAdd : (∫ ω, |f m ω| ∂P) =
      (∫ ω, max (f m ω) (0 : ℝ) ∂P) +
      (∫ ω, max (-f m ω) (0 : ℝ) ∂P) := by
    rw [hEq]
    exact integral_add hIp hIn
  exact ⟨hI, by rw [hAdd]; linarith⟩
