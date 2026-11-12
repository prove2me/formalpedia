-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb20_original_finite_range_mixed_stopped_noise_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:02:00.936016+00:00
-- url     : https://prove2.me/submissions/72e8ea90-cb35-4fbc-a80c-a946b1035dbd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_range_stop_condexp
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The same original finite-range stopped clock has both centred noise sources. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω) :
    ∃ MG MJ : Ω → ℝ,
      Integrable MG P ∧ Integrable MJ P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MG ω = 0) ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MJ ω = 0) ∧
      (∀ ω, MG ω = R (τ ω) ω) ∧
      ∃ Jsmall : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Tendsto
            (fun k : ℕ =>
              avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
            atTop (nhds (Jsmall t ω))) ∧
        (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
        (∀ s t : ℝ≥0, s ≤ t →
          ∀ᵐ ω ∂P,
            condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
        (∀ ω, MJ ω = Jsmall (τ ω) ω) := by
  obtain ⟨hRI, hRzero⟩ :=
    avram_jb20_original_gaussian_finite_range_stop_condexp
      X R hRsource hRint hRmart
      τ hτstop (n : ℝ≥0) hτbound S hτrange
  obtain ⟨J, hJsource, hJint, hJmart, hJI, hJzero⟩ :=
    avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
      X hX hFinite n hn τ hτstop hτbound
  refine ⟨(fun ω => R (τ ω) ω), (fun ω => J (τ ω) ω),
    hRI, hJI, hRzero, hJzero, ?_, ?_⟩
  · intro ω
    rfl
  · exact ⟨J, hJsource, hJint, hJmart, fun ω => rfl⟩
