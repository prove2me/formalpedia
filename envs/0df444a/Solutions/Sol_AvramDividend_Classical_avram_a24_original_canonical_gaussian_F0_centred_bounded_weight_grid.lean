-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_canonical_gaussian_F0_centred_bounded_weight_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:51:12.382488+00:00
-- url     : https://prove2.me/submissions/9023ed31-616b-4d19-8850-2554fee5e573

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_stopped_gaussian_physical_grid_F0_centred
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original stopped Gaussian mesh F0-centred quadratic martingale source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n : ℕ) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    ∀ j : ℕ,
      let δ : ℝ≥0 := (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let S : Finset ℕ := Finset.range (j + 1)
      let τg : ℕ → Ω → ℝ≥0 := fun i ω =>
        min ((i : ℝ≥0) * δ) (σ ω)
      ∀ (hτg : ∀ i ∈ S, ∀ s : ℝ≥0,
          MeasurableSet[𝓕.rightCont s] {ω : Ω | τg i ω ≤ s})
        (G H : ℕ → Ω → ℝ)
        (hGm : ∀ i (hi : i ∈ S),
          Measurable[(isStoppingTime_withTop_of_le_events (τg i)
            (hτg i hi)).measurableSpace] (G i))
        (hHm : ∀ i (hi : i ∈ S),
          Measurable[(isStoppingTime_withTop_of_le_events (τg i)
            (hτg i hi)).measurableSpace] (H i))
        (hGAE : ∀ i ∈ S, AEStronglyMeasurable (G i) P)
        (hHAE : ∀ i ∈ S, AEStronglyMeasurable (H i) P)
        (BG BH : ℕ → ℝ)
        (hGB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ BG i)
        (hHB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ BH i),
      let M : ℕ → Ω → ℝ := fun i ω =>
        X.X (τg i ω + δ) ω - X.X (τg i ω) ω - (δ : ℝ) * X.c
      let Q : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (G i ω * M i ω +
          (H i ω * (M i ω)^2 - (δ : ℝ) * X.σ^2 * H i ω))
      Integrable Q P ∧
      condExp (𝓕.rightCont 0) P Q =ᵐ[P] (fun _ => (0 : ℝ)):= by
  intro j
  dsimp
  intro hτg G H hGm hHm hGAE hHAE BG BH hGB hHB
  let δ : ℝ≥0 := (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
  let τg : ℕ → Ω → ℝ≥0 := fun i ω =>
    min ((i : ℝ≥0) * δ) (σ ω)
  let M : ℕ → Ω → ℝ := fun i ω =>
    X.X (τg i ω + δ) ω - X.X (τg i ω) ω - (δ : ℝ) * X.c
  have hb (i : ℕ) (hi : i ∈ Finset.range (j + 1)) (ω : Ω) :
      τg i ω ≤ (n : ℝ≥0) :=
    (avram_a24_original_canonical_gaussian_grid_joint_stop_and_horizon
      σ hσstop n hσbound).2.1 j i ω
  have hMI (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
      Integrable (M i) P :=
    (avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
      X hν σ hσstop n hσbound j i).1
  have hM2I (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
      Integrable (fun ω => (M i ω)^2) P :=
    (avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
      X hν σ hσstop n hσbound j i).2.2.1
  have hMsource : M = fun i ω =>
      (X.X (τg i ω + δ) ω - ((τg i ω + δ) : ℝ) * X.c) -
      (X.X (τg i ω) ω - (τg i ω : ℝ) * X.c) := by
    funext i ω
    dsimp [M]
    push_cast
    ring
  exact avram_a20_original_bounded_stopped_gaussian_physical_grid_F0_centred
    X hν (Finset.range (j + 1)) τg hτg
    (fun _ => (n : ℝ≥0)) hb (fun _ => δ)
    G H hGm hHm M hMsource hMI hM2I
    hGAE hHAE BG BH hGB hHB
