-- Prove2me | solution 1 for AvramDividend.Classical.avram_b63_original_B25_two_noise_canonical_dominators_strict_event_gap_impossible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:16:28.697472+00:00
-- url     : https://prove2.me/submissions/ce27ebc6-bb42-4c9d-9a60-2a1b83455c5b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_B25_bounded_mesh_limit_centred_no_positive_event_cash_gap
import Theorems.Thm_AvramDividend_Classical_avram_b61_original_B25_integrable_dominated_intrinsic_physical_gain_limit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (F MG MJ BG BJ : Ω → ℝ)
    (b δ : ℝ) (hδ : 0 < δ)
    (G J E : ℕ → Ω → ℝ)
    (hFI : Integrable F P)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ᵐ ω ∂P, ∀ k, ‖G k ω‖ ≤ BG ω)
    (hJdom : ∀ᵐ ω ∂P, ∀ k, ‖J k ω‖ ≤ BJ ω)
    (hGlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJlim : ∀ᵐ ω ∂P,
      Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hElim : ∀ᵐ ω ∂P,
      Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)))
    (hCashAll : ∀ᵐ ω ∂P, ∀ k,
      F ω ≤ b + G k ω + J k ω + E k ω)
    (hGcenter : ∀ k, (∫ ω in A, G k ω ∂P) = 0)
    (hJcenter : ∀ k, (∫ ω in A, J k ω ∂P) = 0)
    (hGap : (∫ ω in A, (fun (_ : Ω) => b) ω ∂P) + δ ≤
      (∫ ω in A, F ω ∂P)) :
    False := by
  have hMGI : Integrable MG P :=
    avram_b61_original_B25_integrable_dominated_intrinsic_physical_gain_limit
      G MG BG (fun k => (hGI k).aestronglyMeasurable)
      hBG hGdom hGlim
  have hMJI : Integrable MJ P :=
    avram_b61_original_B25_integrable_dominated_intrinsic_physical_gain_limit
      J MJ BJ (fun k => (hJI k).aestronglyMeasurable)
      hBJ hJdom hJlim
  have hGdom' : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω := by
    intro k
    filter_upwards [hGdom] with ω h
    exact h k
  have hJdom' : ∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω := by
    intro k
    filter_upwards [hJdom] with ω h
    exact h k
  exact avram_b60_original_B25_bounded_mesh_limit_centred_no_positive_event_cash_gap
    P A F MG MJ BG BJ b δ hδ G J E
    hFI hGI hJI hMGI hMJI hBG hBJ
    hGdom' hJdom' hGlim hJlim hElim hCashAll
    hGcenter hJcenter hGap
