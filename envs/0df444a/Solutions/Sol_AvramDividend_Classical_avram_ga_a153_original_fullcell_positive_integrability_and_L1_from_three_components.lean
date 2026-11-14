-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a153_original_fullcell_positive_integrability_and_L1_from_three_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:26:55.67775+00:00
-- url     : https://prove2.me/submissions/82913e53-cd97-42b1-9542-0bbf4c646775

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a136_original_gaussian_fullcell_positive_three_source_errors_L1_glue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- Full pre-stop source spatial positive residual is integrable and expected-L1 small from the three original Gaussian one-sided component budgets. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F T B C : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, F m ω = T m ω + B m ω + C m ω)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω => max (F m ω) 0) P)
    (hTI : ∀ m, Integrable (fun ω => max (T m ω) 0) P)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hTt : Tendsto (fun m => ∫ ω, max (T m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    (∀ m, Integrable (fun ω => max (F m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hPoint (m : ℕ) (ω : Ω) :
      max (F m ω) 0 ≤ max (T m ω) 0 + |B m ω| + max (C m ω) 0 := by
    rw [hSplit m ω]
    apply max_le
    · linarith [le_max_left (T m ω) 0, le_abs_self (B m ω),
        le_max_left (C m ω) 0]
    · linarith [le_max_right (T m ω) 0, abs_nonneg (B m ω),
        le_max_right (C m ω) 0]
  have hFI : ∀ m, Integrable (fun ω => max (F m ω) 0) P := by
    intro m
    have hEnvelope := ((hTI m).add (hBI m)).add (hCI m)
    apply Integrable.mono' hEnvelope (hMeas m)
    filter_upwards [] with ω
    change ‖max (F m ω) 0‖ ≤
      max (T m ω) 0 + |B m ω| + max (C m ω) 0
    have hPos : 0 ≤ max (F m ω) (0 : ℝ) :=
      le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hPos]
    exact hPoint m ω
  refine ⟨hFI, ?_⟩
  exact avram_ga_a136_original_gaussian_fullcell_positive_three_source_errors_L1_glue
    P F T B C hSplit hFI hTI hBI hCI hTt hBt hCt
