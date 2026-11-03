-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_C2_source_taylor_expected_jump_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:20:34.630489+00:00
-- url     : https://prove2.me/submissions/2785bbdf-38b1-4eb1-abf0-3a00c4522cd7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-!
Original-process controlled C² finite mesh expected jump identity.
Gaussian half-bracket cancellation is proved under explicit source extraction.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) :
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
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let A : ι → Ω → ℝ := fun i ω =>
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
    let J : ι → Ω → ℝ := fun i ω =>
      (Jsmall (τ i ω + h i) ω - Jsmall (τ i ω) ω) +
      (Jlarge (τ i ω + h i) ω - Jlarge (τ i ω) ω)
    let Full : Ω → ℝ := fun ω => Finset.sum S (fun i =>
      G i ω * A i ω +
        (1 / 2 : ℝ) * H i ω * (A i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))
    let Jump : Ω → ℝ := fun ω => Finset.sum S (fun i =>
      G i ω * J i ω + H i ω * V i ω * J i ω +
        (1 / 2 : ℝ) * H i ω * J i ω ^ 2)
    (∀ i ∈ S, Integrable (fun ω => G i ω * V i ω) P) →
    (∀ i ∈ S, Integrable (fun ω => (1 / 2 : ℝ) * H i ω) P) →
    (∀ i ∈ S, Integrable (fun ω =>
      ((1 / 2 : ℝ) * H i ω) * V i ω ^ 2) P) →
    Integrable Jump P →
    Integrable Full P ∧ (∫ ω, Full ω ∂P) = (∫ ω, Jump ω ∂P) := by
  classical
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
         if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
      (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
  let A : ι → Ω → ℝ := fun i ω =>
    X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
  let V : ι → Ω → ℝ := fun i ω =>
    Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
  let J : ι → Ω → ℝ := fun i ω =>
    (Jsmall (τ i ω + h i) ω - Jsmall (τ i ω) ω) +
    (Jlarge (τ i ω + h i) ω - Jlarge (τ i ω) ω)
  dsimp only
  intro hGI hHI hH2I hJumpInt
  let HH : ι → Ω → ℝ := fun i ω => (1 / 2 : ℝ) * H i ω
  have hMean :=
    avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      x D hD w C hw q T S τ hτ B hbounded h G HH
      (by intro i hi; rfl) (by intro i hi; rfl) hGI hHI hH2I
  dsimp only at hMean
  let Gauss : Ω → ℝ := fun ω => Finset.sum S (fun i => G i ω * V i ω + (1 / 2 : ℝ) * H i ω * (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))
  have hGaussEq : Gauss = (fun ω => Finset.sum S (fun i => G i ω * V i ω + (HH i ω * V i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * HH i ω))) := by
    funext ω; apply Finset.sum_congr rfl
    intro i hi; dsimp [HH]; ring
  have hGaussInt : Integrable Gauss P := by rw [hGaussEq]; exact hMean.1
  have hGaussZero : (∫ ω, Gauss ω ∂P) = 0 := by rw [hGaussEq]; exact hMean.2
  let M : ℝ≥0 → Ω → ℝ := fun t ω => Y.X t ω - (t : ℝ) * Y.c
  let BM : ι → Ω → ℝ := fun i ω =>
    M (τ i ω + h i) ω - M (τ i ω) ω
  have hBM : ∀ i ∈ S, ∀ ω, BM i ω = V i ω := by
    intro i hi ω; dsimp [BM, M, V]
    ring
  have hPath :=
    avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
      X x D hD w C hw q T M Jsmall Jlarge
      (by intro t ω; exact hSourceDecomp t ω) S τ hτ h
  dsimp only at hPath
  let Full : Ω → ℝ := fun ω => Finset.sum S (fun i => G i ω * A i ω + (1 / 2 : ℝ) * H i ω * (A i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))
  let Jump : Ω → ℝ := fun ω => Finset.sum S (fun i => G i ω * J i ω + H i ω * V i ω * J i ω + (1 / 2 : ℝ) * H i ω * J i ω ^ 2)
  have hFull : Full = Gauss + Jump := by
    funext ω
    calc
      Full ω =
          (Finset.sum S (fun i => G i ω * BM i ω + (1 / 2 : ℝ) * H i ω * (BM i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) +
          (Finset.sum S (fun i => G i ω * J i ω + H i ω * BM i ω * J i ω + (1 / 2 : ℝ) * H i ω * J i ω ^ 2)) := hPath ω
      _ = Gauss ω + Jump ω := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi; rw [hBM i hi ω]
        · apply Finset.sum_congr rfl
          intro i hi; rw [hBM i hi ω]
  have hFullInt : Integrable Full P := by
    rw [hFull]; exact hGaussInt.add hJumpInt
  change Integrable Full P ∧ (∫ ω, Full ω ∂P) = (∫ ω, Jump ω ∂P)
  refine ⟨hFullInt, ?_⟩
  calc
    (∫ ω, Full ω ∂P) = ∫ ω, Gauss ω + Jump ω ∂P := by
      rw [hFull]
      simp only [Pi.add_apply]
    _ = (∫ ω, Gauss ω ∂P) + (∫ ω, Jump ω ∂P) :=
      integral_add hGaussInt hJumpInt
    _ = ∫ ω, Jump ω ∂P := by
      rw [hGaussZero]
      simp
