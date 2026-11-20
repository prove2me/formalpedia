-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_true_source_joint_geometric_gaussian_smallmark_centered_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:36:40.420961+00:00
-- url     : https://prove2.me/submissions/b9098aa2-455e-4499-bba5-9f4e8d560753

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b25_two_noise_L1_cauchy_geometric_ae_domination
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_centered_mesh_limit_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

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
      N ≤ m → (∫ ω, ‖E m ω‖ ∂P) ≤ ε)
    (hGcenter : ∀ k, (∫ ω, G k ω ∂ P) = 0)
    (hJcenter : ∀ k, (∫ ω, J k ω ∂ P) = 0) :
    ∃ (K : ℕ → ℕ) (MG MJ BG BJ : Ω → ℝ),
      StrictMono K ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => G (K k) ω) atTop (𝓝 (MG ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => J (K k) ω) atTop (𝓝 (MJ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => E (K k) ω) atTop (𝓝 (0 : ℝ))) ∧
      Integrable BG P ∧ Integrable BJ P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖G (K k) ω‖ ≤ BG ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖J (K k) ω‖ ≤ BJ ω) ∧
      (∫ ω, MG ω ∂ P) = 0 ∧
      (∫ ω, MJ ω ∂ P) = 0 := by
  obtain ⟨K, MG, MJ, BG, BJ, hK, hGA, hJA, hEA, hBGI, hBJI,
      hGB, hJB⟩ :=
    avram_b25_two_noise_L1_cauchy_geometric_ae_domination
      P G J E hGI hJI hEI hGC hJC hEC
  refine ⟨K, MG, MJ, BG, BJ, hK, hGA, hJA, hEA, hBGI, hBJI,
    hGB, hJB, ?_, ?_⟩
  . exact avram_p3_c_bvchain_dominated_centered_mesh_limit_mean_zero
      P (fun k => G (K k)) MG BG
      (fun k => (hGI (K k)).aestronglyMeasurable)
      hBGI hGB hGA (fun k => hGcenter (K k))
  . exact avram_p3_c_bvchain_dominated_centered_mesh_limit_mean_zero
      P (fun k => J (K k)) MJ BJ
      (fun k => (hJI (K k)).aestronglyMeasurable)
      hBJI hJB hJA (fun k => hJcenter (K k))
