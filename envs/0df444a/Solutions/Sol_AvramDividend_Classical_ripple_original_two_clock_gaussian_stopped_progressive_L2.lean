-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_two_clock_gaussian_stopped_progressive_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:41:33.077813+00:00
-- url     : https://prove2.me/submissions/e2526d78-e82b-46dc-b7d0-555d311b4392

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ripple_between_stopping_times_predictable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_ripple_original_physical_time_two_clock_Gaussian_MemLp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
      (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
      (p.1 : WithTop ℝ≥0) ≤ τ p.2}
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      IsStronglyProgressive 𝓕.rightCont
        (fun t ω => S.indicator G (t,ω)) ∧
      MemLp (S.indicator G) 2 μ := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  let S : Set (ℝ≥0 × Ω) := {p | 0 < p.1 ∧
    (σ p.2 : WithTop ℝ≥0) < (p.1 : WithTop ℝ≥0) ∧
    (p.1 : WithTop ℝ≥0) ≤ τ p.2}
  obtain ⟨μ, hμ, hPhysical, hLp⟩ :=
    ripple_original_physical_time_two_clock_Gaussian_MemLp
      X x D hD w a b u v hw hau huv hvb T σ τ hσstop hτstop
  have hμ0 : (0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) Set.univ < ⊤ := by
    simp
  have hG : Measurable[𝓕.rightCont.predictable] G :=
    (avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
      X x D hD w a b u v hw hau huv hvb 0 hμ0).1
  have hS : MeasurableSet[𝓕.rightCont.predictable] S :=
    ripple_between_stopping_times_predictable 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))
      (fun ω => (τ ω : WithTop ℝ≥0)) hσstop hτstop
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hPred : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => S.indicator G (t,ω)) := by
    change StronglyMeasurable (S.indicator G)
    exact (hG.indicator hS).stronglyMeasurable
  exact ⟨μ, hμ, hPhysical, hPred.isStronglyProgressive, hLp⟩
