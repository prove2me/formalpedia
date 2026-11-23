-- Prove2me | solution 1 for AvramDividend.Classical.avram_b60_original_B25_bounded_mesh_limit_centred_no_positive_event_cash_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:13:04.763194+00:00
-- url     : https://prove2.me/submissions/30baddd6-506d-4e9a-86e4-f53e40ccfc6a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b58_original_signed_B25_ae_pointwise_three_error_limits_pass_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_b59_original_B25_dominated_centered_event_mesh_limit_mean_zero
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
    (hMGI : Integrable MG P)
    (hMJI : Integrable MJ P)
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω)
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω)
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
  have hCash :=
    avram_b58_original_signed_B25_ae_pointwise_three_error_limits_pass_cash_bound
      F MG MJ b G J E hGlim hJlim hElim hCashAll
  have hGc :=
    avram_b59_original_B25_dominated_centered_event_mesh_limit_mean_zero
      A G MG BG hGI hBG hGdom hGlim hGcenter
  have hJc :=
    avram_b59_original_B25_dominated_centered_event_mesh_limit_mean_zero
      A J MJ BJ hJI hBJ hJdom hJlim hJcenter
  have hFA : Integrable F (P.restrict A) :=
    hFI.mono_measure Measure.restrict_le_self
  have hMA : Integrable MG (P.restrict A) :=
    hMGI.mono_measure Measure.restrict_le_self
  have hJA : Integrable MJ (P.restrict A) :=
    hMJI.mono_measure Measure.restrict_le_self
  have hConst : Integrable (fun (_ : Ω) => b) (P.restrict A) :=
    integrable_const b
  have hBound :
      (∫ ω in A, F ω ∂P) ≤
        (∫ ω in A, b + MG ω + MJ ω ∂P) := by
    exact integral_mono_ae hFA ((hConst.add hMA).add hJA)
      (ae_restrict_of_ae hCash)
  have hRight :
      (∫ ω in A, b + MG ω + MJ ω ∂P) =
        (∫ ω in A, (fun (_ : Ω) => b) ω ∂P) := by
    have hI1 :
        (∫ ω in A, b + MG ω + MJ ω ∂P) =
          (∫ ω in A, b + MG ω ∂P) +
            (∫ ω in A, MJ ω ∂P) := by
      simpa only [Pi.add_apply] using
        (integral_add (hConst.add hMA) hJA)
    have hI2 :
        (∫ ω in A, b + MG ω ∂P) =
          (∫ ω in A, (fun (_ : Ω) => b) ω ∂P) +
            (∫ ω in A, MG ω ∂P) := by
      simpa only [Pi.add_apply] using (integral_add hConst hMA)
    calc
      (∫ ω in A, b + MG ω + MJ ω ∂P) =
          (∫ ω in A, b + MG ω ∂P) +
            (∫ ω in A, MJ ω ∂P) := hI1
      _ = (∫ ω in A, (fun (_ : Ω) => b) ω ∂P) := by
        rw [hI2, hGc, hJc]
        ring
  rw [hRight] at hBound
  linarith
