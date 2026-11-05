-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_Taylor_compensated_mean_zero_from_P2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:46:33.673206+00:00
-- url     : https://prove2.me/submissions/4084d20b-6ebc-48d6-8206-0d59178385c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_pathwise_compensator_L1_mean_zero_canonical_bands
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_source_future_of_P2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    ∀ (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (q : ℝ) (hq : 0 ≤ q),
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let η : Measure ℝ≥0 := (((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal)
    let Comp : Ω → ℝ := fun ω =>
      ∫ t, ∫ z, GW ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂η
    let Jump : Ω → ℝ := fun ω =>
      ∫ p, GW ((p.1, ω), p.2) ∂(NX ω)
    Integrable (fun ω => Jump ω - Comp ω) P ∧
    (∫ ω, (Jump ω - Comp ω) ∂P) = 0) := by
  classical
  obtain ⟨μ, hμfin, hμclock, hMain⟩ :=
    avram_wave6_02_actual_discounted_ruin_stopped_Taylor_pathwise_compensator_L1_mean_zero_canonical_bands
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv T
  refine ⟨μ, hμfin, hμclock, ?_⟩
  intro NX K M hM S hST MT N hMT hN q hq
    a Y J HS GW η Comp Jump
  have hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (B : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet B →
        MT ((Set.Ioi i ×ˢ A) ×ˢ B) =
          N ((Set.Ioi i ×ˢ A) ×ˢ B) := by
    intro i A B hA hB
    have hRect :=
      avram_p4_f_assembly_original_rightcont_source_future_of_P2
        X T NX (by intro ω; rfl) K (by intro ω; rfl)
        M hM μ hμclock N hN i A hA B hB
    simpa only [hMT, hST] using hRect
  exact hMain M hM S hST MT N hMT hN hFuture q hq
