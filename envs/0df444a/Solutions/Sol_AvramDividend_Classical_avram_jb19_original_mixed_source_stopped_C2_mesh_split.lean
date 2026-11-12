-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb19_original_mixed_source_stopped_C2_mesh_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:41:08.88027+00:00
-- url     : https://prove2.me/submissions/9c976dd7-f6f3-4320-90b1-582643925d44

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_residual_totalise_source_path
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Apply the original physical source decomposition to the full stopped
C2 Gaussian and marked-jump finite-mesh Taylor identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (h : ι → ℝ≥0) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
      let G : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
      let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then
               iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
      let A : ι → Ω → ℝ := fun i ω =>
        X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
      let B : ι → Ω → ℝ := fun i ω =>
        M (τ i ω + h i) ω - M (τ i ω) ω
      let J : ι → Ω → ℝ := fun i ω =>
        (Jsmall (τ i ω + h i) ω - Jsmall (τ i ω) ω) +
        (avram_p4_h_gaussian_intrinsic_large_jump_sum X
            (τ i ω + h i) ω -
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ i ω) ω)
      ∀ ω,
        Finset.sum S (fun i => G i ω * A i ω +
          (1 / 2 : ℝ) * H i ω *
            (A i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) =
        Finset.sum S (fun i => G i ω * B i ω +
          (1 / 2 : ℝ) * H i ω *
            (B i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) +
        Finset.sum S (fun i =>
          G i ω * J i ω + H i ω * B i ω * J i ω +
            (1 / 2 : ℝ) * H i ω * J i ω ^ 2) := by
  classical
  obtain ⟨M, hpath, hMeq⟩ :=
    avram_jb19_original_gaussian_residual_totalise_source_path
      X R Jsmall hRsource hJsource
  refine ⟨M, hpath, hMeq, ?_⟩
  exact
    avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
      X x D hD w C hw q T M Jsmall
      (avram_p4_h_gaussian_intrinsic_large_jump_sum X)
      hpath S τ hτ h
