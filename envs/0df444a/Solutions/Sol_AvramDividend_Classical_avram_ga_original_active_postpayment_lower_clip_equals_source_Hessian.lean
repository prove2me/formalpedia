-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_active_postpayment_lower_clip_equals_source_Hessian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:38:11.077181+00:00
-- url     : https://prove2.me/submissions/74c56c71-4c72-48e6-9343-0c607935c628

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} (δ b q : ℝ) (hδ : 0 < δ)
    (w : ℝ → ℝ) (Y : ℕ → Ω → ℝ)
    (s : ℕ → ℝ≥0) (ρ : Ω → ℝ≥0)
    (hFloor : ∀ (i : ℕ) (ω : Ω), s i < ρ ω → δ ≤ Y i ω) :
    ∀ (i : ℕ) (ω : Ω),
      (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ω ∈ Icc (δ / 2) b then iteratedDeriv 2 w (Y i ω) else 0)
      else 0) =
      (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ω ≤ b then iteratedDeriv 2 w (Y i ω) else 0)
      else 0) := by
  intro i ω
  by_cases hs : s i < ρ ω
  · have hlo : δ / 2 ≤ Y i ω := by
      linarith [hFloor i ω hs]
    by_cases hb : Y i ω ≤ b
    · simp [hs, Set.mem_Icc, hlo, hb]
    · simp [hs, Set.mem_Icc, hb]
  · simp [hs]
