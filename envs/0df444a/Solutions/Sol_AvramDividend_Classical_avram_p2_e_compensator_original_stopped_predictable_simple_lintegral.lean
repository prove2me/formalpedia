-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_stopped_predictable_simple_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:35:47.979194+00:00
-- url     : https://prove2.me/submissions/fc0539ff-9b35-4af6-ab18-f5e22e8409db

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_rightcont_stopped_future_rect

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The stopped original source and compensator agree on positive simple integrals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω = ((Measure.count.restrict
      {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    {ι : Type*} (S : Finset ι)
    (i : ι → ℝ≥0) (A : ι → Set Ω)
    (hA : ∀ k ∈ S, MeasurableSet[𝓕.rightCont (i k)] (A k))
    (B : ι → Set ℝ) (hB : ∀ k ∈ S, MeasurableSet (B k))
    (E : ι → Set ((ℝ≥0 × Ω) × ℝ))
    (hE : ∀ k ∈ S, E k = (Ioi (i k) ×ˢ A k) ×ˢ B k)
    (hEm : ∀ k ∈ S, MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] (E k))
    (w : ι → ℝ≥0∞) :
    (∫⁻ p, ∑ k ∈ S, (E k).indicator (fun _ => w k) p
        ∂(M.restrict {p | p.1.1 ≤ T})) =
      ∫⁻ p, ∑ k ∈ S, (E k).indicator (fun _ => w k) p ∂N := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    @Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)
  have hmeas (k : ι) (hk : k ∈ S) :
      Measurable ((E k).indicator (fun _ => w k)) :=
    measurable_const.indicator (hEm k hk)
  have hcell (k : ι) (hk : k ∈ S) :
      (∫⁻ p, (E k).indicator (fun _ => w k) p
        ∂(M.restrict {p | p.1.1 ≤ T})) =
        ∫⁻ p, (E k).indicator (fun _ => w k) p ∂N := by
    have heq :
        (M.restrict {p | p.1.1 ≤ T}) (E k) = N (E k) := by
      rw [hE k hk]
      exact avram_p2_e_compensator_original_rightcont_stopped_future_rect
        X T NX hNX K hK M hM μ hμclock N hN
        (i k) (A k) (hA k hk) (B k) (hB k hk)
    have hleft :
        (∫⁻ p, (E k).indicator (fun _ => w k) p
          ∂(M.restrict {p | p.1.1 ≤ T})) =
        w k * (M.restrict {p | p.1.1 ≤ T}) (E k) :=
      lintegral_indicator_const (μ := M.restrict {p | p.1.1 ≤ T})
        (hEm k hk) (w k)
    have hright :
        (∫⁻ p, (E k).indicator (fun _ => w k) p ∂N) =
        w k * N (E k) :=
      lintegral_indicator_const (μ := N) (hEm k hk) (w k)
    calc
      _ = w k * (M.restrict {p | p.1.1 ≤ T}) (E k) := hleft
      _ = w k * N (E k) := congrArg (fun v : ℝ≥0∞ => w k * v) heq
      _ = _ := hright.symm
  calc
    (∫⁻ p, ∑ k ∈ S, (E k).indicator (fun _ => w k) p
      ∂(M.restrict {p | p.1.1 ≤ T})) =
      ∑ k ∈ S, ∫⁻ p, (E k).indicator (fun _ => w k) p
        ∂(M.restrict {p | p.1.1 ≤ T}) :=
        lintegral_finset_sum S hmeas
    _ = ∑ k ∈ S, ∫⁻ p, (E k).indicator (fun _ => w k) p ∂N :=
      Finset.sum_congr rfl hcell
    _ = _ := (lintegral_finset_sum S hmeas).symm
