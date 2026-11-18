-- Prove2me | solution 2 for AvramDividend.Classical.avram_gbB62_original_eventwise_L1_noise_limit_inherits_path_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:03:38.200297+00:00
-- url     : https://prove2.me/submissions/af838a22-0d1c-480c-9b22-07bd936bf434

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB61_L1_limit_inherits_uniform_gaussian_mesh_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- An L1 source inherits tube bounds after restricting to the source event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (N : Ω → ℝ) (M : ℕ → Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hBound : ∀ m ω, ω ∈ A → |M m ω| ≤ ε)
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by
  classical
  let M' : ℕ → Ω → ℝ := fun m ω => if ω ∈ A then M m ω else 0
  have hMAE (m : ℕ) : M' m =ᵐ[P.restrict A] M m := by
    filter_upwards [ae_restrict_mem hA] with ω hω
    simp [M', hω]
  have hMI' (m : ℕ) : Integrable (M' m) (P.restrict A) :=
    (hMI m).congr (hMAE m).symm
  have hBound' (m : ℕ) (ω : Ω) : |M' m ω| ≤ ε := by
    by_cases h : ω ∈ A
    · simpa [M', h] using hBound m ω h
    · simpa [M', h] using hε
  have hL1' : Tendsto
      (fun m => ∫ ω, |N ω - M' m ω| ∂(P.restrict A))
      atTop (𝓝 (0 : ℝ)) := by
    have heq :
        (fun m => ∫ ω, |N ω - M' m ω| ∂(P.restrict A)) =
        (fun m => ∫ ω in A, |N ω - M m ω| ∂P) := by
      funext m
      apply integral_congr_ae
      filter_upwards [hMAE m] with ω hm
      simp [hm]
    rw [heq]
    exact hL1
  exact avram_gbB61_L1_limit_inherits_uniform_gaussian_mesh_bound
    (P.restrict A) N M' ε hε hNI hMI' hBound' hL1'
