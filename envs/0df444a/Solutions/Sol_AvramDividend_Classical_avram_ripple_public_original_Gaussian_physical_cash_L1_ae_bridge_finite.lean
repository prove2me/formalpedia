-- Prove2me | solution 1 for AvramDividend.Classical.avram_ripple_public_original_Gaussian_physical_cash_L1_ae_bridge_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:43:58.16888+00:00
-- url     : https://prove2.me/submissions/b4eb8e2c-36c4-4356-84fc-01557c8b5edb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ripple_public_signed_L1_mesh_ae_upper
import Theorems.Thm_AvramDividend_Classical_avram_ga_discount_cash_integrable_finite_measure
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_global_GH_L1_limit_restricts_to_future_tube
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (F N Occ : Ω → ℝ) (M E : ℕ → Ω → ℝ) (x Γ c : ℝ)
    (hFI : Integrable F P) (hMI : ∀ m, Integrable (M m) P)
    (hOI : Integrable Occ (P.restrict A)) (hNI : Integrable N P)
    (hEI : ∀ m, Integrable (E m) (P.restrict A))
    (hEpos : ∀ m, ∀ᵐ ω ∂(P.restrict A), 0 ≤ E m ω)
    (hEL1 : Tendsto (fun m => ∫ ω in A, E m ω ∂P) atTop (nhds (0 : ℝ)))
    (hML1 : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂P)
      atTop (nhds (0 : ℝ)))
    (hCash : ∀ m, ∀ᵐ ω ∂(P.restrict A),
      F ω - x - (Γ + c * Occ ω) ≤ M m ω + E m ω) :
    (∀ᵐ ω ∂(P.restrict A), F ω - x ≤ N ω + Γ + c * Occ ω) ∧
    Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by
  classical
  have hFA : Integrable F (P.restrict A) :=
    hFI.mono_measure Measure.restrict_le_self
  have hNA : Integrable N (P.restrict A) :=
    hNI.mono_measure Measure.restrict_le_self
  have hQ : Integrable
      (fun ω => F ω - x - (Γ + c * Occ ω) - N ω) (P.restrict A) :=
    avram_ga_discount_cash_integrable_finite_measure
      (P.restrict A) F Occ N x Γ c hFA hOI hNA
  have hGPlus : Integrable
      (fun ω => (1 / 2 : ℝ) *
        ((F ω - x - (Γ + c * Occ ω) - N ω) +
          |F ω - x - (Γ + c * Occ ω) - N ω|))
        (P.restrict A) :=
    MeasureTheory.Integrable.const_mul
      (MeasureTheory.Integrable.add hQ (MeasureTheory.Integrable.abs hQ))
      (1 / 2 : ℝ)
  have hGI : Integrable
      (fun ω => max ((F ω - (Γ + c * Occ ω)) - x - N ω) 0)
        (P.restrict A) := by
    convert hGPlus using 1
    funext ω
    have hmax (v : ℝ) :
        max v 0 = (1 / 2 : ℝ) * (v + |v|) := by
      rcases le_total 0 v with hv | hv
      · rw [max_eq_left hv, abs_of_nonneg hv]
        ring
      · rw [max_eq_right hv, abs_of_nonpos hv]
        ring
    have hv : (F ω - (Γ + c * Occ ω)) - x - N ω =
        F ω - x - (Γ + c * Occ ω) - N ω := by ring
    rw [hv, hmax]
  have hNI_diff (m : ℕ) :
      Integrable (fun ω => |M m ω - N ω|) (P.restrict A) :=
    (((hMI m).sub hNI).abs).mono_measure Measure.restrict_le_self
  have hEIabs (m : ℕ) :
      Integrable (fun ω => |E m ω|) (P.restrict A) := (hEI m).abs
  have hEL1abs :
      Tendsto (fun m => ∫ ω in A, |E m ω| ∂P)
        atTop (nhds (0 : ℝ)) := by
    convert hEL1 using 1
    funext m
    apply integral_congr_ae
    filter_upwards [hEpos m] with ω h
    simp only [abs_of_nonneg h]
  have hML1A :=
    avram_gaussianB_original_global_GH_L1_limit_restricts_to_future_tube
      P M N (fun m => ((hNI.sub (hMI m)).abs)) hML1 A hA
  have hML1A' : Tendsto (fun m => ∫ ω in A, |M m ω - N ω| ∂P)
      atTop (nhds (0 : ℝ)) := by
    simpa only [abs_sub_comm] using hML1A
  have hPath : ∀ m, ∀ᵐ ω ∂(P.restrict A),
      (F ω - (Γ + c * Occ ω)) - x ≤ M m ω + E m ω := by
    intro m
    filter_upwards [hCash m] with ω h
    linarith
  have hBound := avram_ripple_public_signed_L1_mesh_ae_upper
    P A (fun ω => F ω - (Γ + c * Occ ω)) N M E x
    hGI hNI_diff hEIabs hPath hML1A' hEL1abs
  refine ⟨?_, hML1A⟩
  filter_upwards [hBound] with ω h
  linarith
