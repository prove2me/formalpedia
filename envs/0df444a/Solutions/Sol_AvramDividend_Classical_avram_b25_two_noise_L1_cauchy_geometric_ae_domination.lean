-- Prove2me | solution 1 for AvramDividend.Classical.avram_b25_two_noise_L1_cauchy_geometric_ae_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:06:10.375576+00:00
-- url     : https://prove2.me/submissions/c41de716-ff4f-4caa-9a0a-9bccbf05401c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_simultaneous_geometric_L1_subsequence_from_original_three_cauchy_sources
import Theorems.Thm_AvramDividend_Classical_avram_b25_geometric_L1_two_gain_integrable_ae_envelopes
import Theorems.Thm_AvramDividend_Classical_avram_b25_geometric_integrable_signed_error_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_b25_two_gain_ae_summable_increments_converge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G J E : ℕ → Ω → ℝ)
    (hGI : ∀ m, Integrable (G m) P)
    (hJI : ∀ m, Integrable (J m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hGC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
      N ≤ m → N ≤ l → (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε)
    (hJC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
      N ≤ m → N ≤ l → (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε)
    (hEC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ,
      N ≤ m → (∫ ω, ‖E m ω‖ ∂P) ≤ ε) :
    ∃ (K : ℕ → ℕ) (MG MJ BG BJ : Ω → ℝ),
      StrictMono K ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => G (K k) ω) atTop (𝓝 (MG ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => J (K k) ω) atTop (𝓝 (MJ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => E (K k) ω) atTop (𝓝 (0 : ℝ))) ∧
      Integrable BG P ∧ Integrable BJ P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖G (K k) ω‖ ≤ BG ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖J (K k) ω‖ ≤ BJ ω) := by
  obtain ⟨K,hK,hGstep,hJstep,hEstep⟩ :=
    avram_b24_simultaneous_geometric_L1_subsequence_from_original_three_cauchy_sources
      P G J E hGC hJC hEC
  obtain ⟨BG,BJ,hBGI,hBJI,hGsum,hJsum,hBG,hBJ⟩ :=
    AvramDividend.Classical.avram_b25_geometric_L1_two_gain_integrable_ae_envelopes
      P (fun k => G (K k)) (fun k => J (K k))
      (fun k => hGI (K k)) (fun k => hJI (K k)) hGstep hJstep
  obtain ⟨MG,MJ,hGlimit,hJlimit⟩ :=
    AvramDividend.Classical.avram_b25_two_gain_ae_summable_increments_converge
      P (fun k => G (K k)) (fun k => J (K k)) hGsum hJsum
  have hElimit :=
    AvramDividend.Classical.avram_b25_geometric_integrable_signed_error_ae_zero
      P (fun k => E (K k)) (fun k => hEI (K k)) hEstep
  exact ⟨K, MG, MJ, BG, BJ, hK, hGlimit, hJlimit, hElimit,
    hBGI, hBJI, hBG, hBJ⟩
