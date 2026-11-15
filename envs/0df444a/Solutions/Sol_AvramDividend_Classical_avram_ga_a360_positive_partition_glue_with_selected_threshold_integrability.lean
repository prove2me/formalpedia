-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a360_positive_partition_glue_with_selected_threshold_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:03:48.533586+00:00
-- url     : https://prove2.me/submissions/d50818fa-23d5-434e-9d8e-2df878954eb7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a280_positive_fullcell_integrable_of_measurable_masked_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (S L : ℝ → ℕ → Ω → ℝ)
    (hFm : ∀ m, AEStronglyMeasurable (fun ω => max (F m ω) 0) P)
    (hLI : ∀ δ, 0 < δ → ∀ m,
      Integrable (fun ω => max (L δ m ω) 0) P)
    (hPt : ∀ δ, 0 < δ → ∀ m ω,
      max (F m ω) 0 ≤ max (S δ m ω) 0 + max (L δ m ω) 0)
    (hL : ∀ δ, 0 < δ →
      Tendsto (fun m => ∫ ω, max (L δ m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)))
    (hS : ∀ η, 0 < η →
      ∃ δ, 0 < δ ∧
        (∀ m, Integrable (fun ω => max (S δ m ω) 0) P) ∧
        ∃ k : ℕ, ∀ m, k ≤ m →
          (∫ ω, max (S δ m ω) 0 ∂P) ≤ η) :
    (∀ m, Integrable (fun ω => max (F m ω) 0) P) ∧
      Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  have hOne : (0 : ℝ) < 1 := by norm_num
  obtain ⟨δ₀,hδ₀,hSI₀,k₀,hBudget₀⟩ := hS 1 hOne
  have hFI (m : ℕ) : Integrable (fun ω => max (F m ω) 0) P :=
    avram_ga_a280_positive_fullcell_integrable_of_measurable_masked_partition
      P (F m) (S δ₀ m) (L δ₀ m)
      (hFm m) (hSI₀ m) (hLI δ₀ hδ₀ m) (hPt δ₀ hδ₀ m)
  refine ⟨hFI,?_⟩
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hhalf : 0 < ε/2 := by linarith
  obtain ⟨δ,hδ,hSI,kS,hSmall⟩ := hS (ε/2) hhalf
  obtain ⟨kL,hLarge⟩ :=
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
        integral_mono (hFI m) ((hSI m).add (hLI δ hδ m))
          (hPt δ hδ m)
      _ = (∫ ω, max (S δ m ω) 0 ∂P) +
            (∫ ω, max (L δ m ω) 0 ∂P) :=
        integral_add (hSI m) (hLI δ hδ m)
  have hFpos : 0 ≤ (∫ ω, max (F m ω) 0 ∂P) :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hLpos : 0 ≤ (∫ ω, max (L δ m ω) 0 ∂P) :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hLt : (∫ ω, max (L δ m ω) 0 ∂P) < ε/2 := by
    have h := hLarge m hmL
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hLpos] using h
  change dist (∫ ω, max (F m ω) 0 ∂P) (0 : ℝ) < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hFpos]
  linarith [hSmall m hmS]
