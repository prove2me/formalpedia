-- Prove2me | solution 1 for AvramDividend.Classical.avram_b29_product_event_independent_centered_physical_gain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:11:19.179163+00:00
-- url     : https://prove2.me/submissions/2ef697a4-bdae-48f3-bec6-2825f093a556

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b27_event_independent_surrogate_gain_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped ENNReal

theorem solution
    {ΩB ΩN : Type*} [mB : MeasurableSpace ΩB]
    [mN : MeasurableSpace ΩN]
    (μ : Measure ΩB) (ν : Measure ΩN)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set ΩN) (hA : MeasurableSet A)
    (H : ℕ → ΩB → ℝ) (hHm : ∀ k, Measurable (H k))
    (G : ℕ → ΩB × ΩN → ℝ)
    (hHI : ∀ k, Integrable (fun p : ΩB × ΩN => H k p.1) (μ.prod ν))
    (hSame : ∀ k, ∀ᵐ p ∂((μ.prod ν).restrict {p : ΩB × ΩN | p.2 ∈ A}),
      G k p = H k p.1)
    (hZero : ∀ k, (∫ p, H k p.1 ∂(μ.prod ν)) = 0) :
    ∀ k, (∫ p in {p : ΩB × ΩN | p.2 ∈ A},
      G k p ∂(μ.prod ν)) = 0 := by
  have hm : MeasurableSpace.comap (fun p : ΩB × ΩN => p.2) mN ≤
      (inferInstance : MeasurableSpace (ΩB × ΩN)) := by
    exact measurable_snd.comap_le
  have hAset :
      MeasurableSet[MeasurableSpace.comap (fun p : ΩB × ΩN => p.2) mN]
        {p : ΩB × ΩN | p.2 ∈ A} := by
    change MeasurableSet[MeasurableSpace.comap
      (fun p : ΩB × ΩN => p.2) mN] _
    exact ⟨A, hA, rfl⟩
  have hInd : ∀ k,
      Indep (MeasurableSpace.comap (fun p : ΩB × ΩN => p.2) mN)
        (MeasurableSpace.comap
          (fun p : ΩB × ΩN => H k p.1) inferInstance)
        (μ.prod ν) := by
    intro k
    change Indep
      (MeasurableSpace.comap
        (fun p : ΩB × ΩN => p.2) inferInstance)
      (MeasurableSpace.comap
        (fun p : ΩB × ΩN => H k p.1) inferInstance)
      (μ.prod ν)
    exact (ProbabilityTheory.indepFun_prod (hHm k) measurable_id).symm
  exact avram_b27_event_independent_surrogate_gain_mean_zero
    (μ.prod ν) (MeasurableSpace.comap (fun p : ΩB × ΩN => p.2) mN)
    hm {p : ΩB × ΩN | p.2 ∈ A} hAset
    G (fun k p => H k p.1) hHI hInd hSame hZero
