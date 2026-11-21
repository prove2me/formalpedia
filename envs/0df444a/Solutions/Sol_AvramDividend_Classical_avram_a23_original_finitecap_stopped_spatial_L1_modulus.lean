-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_original_finitecap_stopped_spatial_L1_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T09:00:18.481648+00:00
-- url     : https://prove2.me/submissions/f718ae2f-198e-41e9-9046-5f61752ad5b8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_candidate_compact_absolute_bound
import Theorems.Thm_AvramDividend_Classical_avram_a23_finitecap_modulus
import Theorems.Thm_AvramDividend_Classical_avram_a23_finitecap_scalar_L1_modulus
import Theorems.Thm_AvramDividend_Classical_avram_a23_affine_expectation_upper
import Theorems.Thm_AvramDividend_Classical_avram_a23_affine_modulus_L1_tendsto_zero
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Ici 0))
    (U V : ℕ → Ω → ℝ)
    (hInside : ∀ m, ∀ᵐ ω ∂P,
      0 ≤ U m ω ∧ U m ω ≤ b ∧ 0 ≤ V m ω ∧ V m ω ≤ b)
    (hWI : ∀ m, Integrable (fun ω => |w (U m ω) - w (V m ω)|) P)
    (hDI : ∀ m, Integrable (fun ω => |U m ω - V m ω|) P)
    (hD : Tendsto (fun m => ∫ ω, |U m ω - V m ω| ∂P)
       atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, |w (U m ω) - w (V m ω)| ∂P)
      atTop (nhds (0 : ℝ))  := by
  have hcont : ContinuousOn w (Icc 0 b) :=
    hw_cont.mono (fun z hz => hz.1)
  obtain ⟨K, hK, hBound⟩ :=
    avram_a22_original_finitecap_candidate_compact_absolute_bound
      w b hb hcont
  apply avram_a23_affine_modulus_L1_tendsto_zero
    (fun m => ∫ ω, |w (U m ω) - w (V m ω)| ∂P)
    (fun m => ∫ ω, |U m ω - V m ω| ∂P)
    hD (fun m => integral_nonneg (fun _ => abs_nonneg _))
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ :=
    avram_a23_finitecap_modulus w b ε hb hε hw_cont
  let L : ℝ := 2*K/δ
  refine ⟨L, div_nonneg (by positivity) (le_of_lt hδ), ?_⟩
  intro m
  apply avram_a23_affine_expectation_upper
    (fun ω => |w (U m ω)-w (V m ω)|)
    (fun ω => |U m ω-V m ω|)
    (hWI m) (hDI m) ε L
  filter_upwards [hInside m] with ω h
  have hU : U m ω ∈ Icc 0 b := ⟨h.1, h.2.1⟩
  have hV : V m ω ∈ Icc 0 b := ⟨h.2.2.1, h.2.2.2⟩
  exact avram_a23_finitecap_scalar_L1_modulus
    w b K ε δ hK (le_of_lt hε) hδ
    (fun y hy => hBound y hy.1 hy.2)
    (fun y hy z hz hg =>
      le_of_lt (hmod y z hy.1 hy.2 hz.1 hz.2 hg))
    (U m ω) (V m ω) hU hV
