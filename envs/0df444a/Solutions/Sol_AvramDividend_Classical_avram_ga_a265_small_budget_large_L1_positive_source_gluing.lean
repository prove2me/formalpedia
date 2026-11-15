-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a265_small_budget_large_L1_positive_source_gluing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:57:54.407098+00:00
-- url     : https://prove2.me/submissions/71ebf36a-3a04-459f-9e4d-ec73e58d79a2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (S L : ℝ → ℕ → Ω → ℝ)
    (hFI : ∀ m, Integrable (fun ω => max (F m ω) 0) P)
    (hSI : ∀ δ, 0 < δ → ∀ m,
      Integrable (fun ω => max (S δ m ω) 0) P)
    (hLI : ∀ δ, 0 < δ → ∀ m,
      Integrable (fun ω => max (L δ m ω) 0) P)
    (hPt : ∀ δ, 0 < δ → ∀ m ω,
      max (F m ω) 0 ≤
        max (S δ m ω) 0 + max (L δ m ω) 0)
    (hL : ∀ δ, 0 < δ →
      Tendsto (fun m => ∫ ω, max (L δ m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)))
    (hS : ∀ η, 0 < η →
      ∃ δ, 0 < δ ∧ ∃ k : ℕ, ∀ m, k ≤ m →
        (∫ ω, max (S δ m ω) 0 ∂P) ≤ η) :
    Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hhalf : 0 < ε/2 := by linarith
  obtain ⟨δ,hδ,kS,hSsmall⟩ := hS (ε/2) hhalf
  obtain ⟨kL,hLsmall⟩ :=
    (Metric.tendsto_atTop.1 (hL δ hδ)) (ε/2) hhalf
  refine ⟨max kS kL,?_⟩
  intro m hm
  have hmS : kS ≤ m := le_trans (le_max_left _ _) hm
  have hmL : kL ≤ m := le_trans (le_max_right _ _) hm
  have hUpper :
      (∫ ω, max (F m ω) 0 ∂P) ≤
      (∫ ω, max (S δ m ω) 0 ∂P) +
        (∫ ω, max (L δ m ω) 0 ∂P) := by
    calc
      (∫ ω, max (F m ω) 0 ∂P) ≤
          ∫ ω, max (S δ m ω) 0+max (L δ m ω) 0 ∂P :=
        integral_mono (hFI m)
          ((hSI δ hδ m).add (hLI δ hδ m)) (hPt δ hδ m)
      _ = (∫ ω, max (S δ m ω) 0 ∂P) +
            (∫ ω, max (L δ m ω) 0 ∂P) :=
        integral_add (hSI δ hδ m) (hLI δ hδ m)
  have hFpos : 0 ≤ (∫ ω, max (F m ω) 0 ∂P) :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hLpos : 0 ≤ (∫ ω, max (L δ m ω) 0 ∂P) :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hLt : (∫ ω, max (L δ m ω) 0 ∂P) < ε/2 := by
    have h := hLsmall m hmL
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hLpos] using h
  change dist (∫ ω, max (F m ω) 0 ∂P) (0 : ℝ) < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hFpos]
  linarith [hSsmall m hmS]
