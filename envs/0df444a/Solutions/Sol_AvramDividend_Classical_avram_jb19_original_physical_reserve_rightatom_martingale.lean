-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb19_original_physical_reserve_rightatom_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:39:15.10602+00:00
-- url     : https://prove2.me/submissions/d816746f-460e-4af6-9c3e-eee5fa905969

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_source_totalised_martingale_bracket
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Carry the original Gaussian source certificate into the physical reserve,
retaining the dividend right-payment atom at each time and sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P)
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (hRbracket : ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
      (∀ t : ℝ≥0,
        AEStronglyMeasurable[𝓕.rightCont t] (M t) P) ∧
      (∀ t : ℝ≥0, Integrable (M t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (M t) ω = M s ω) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ω => (M t ω) ^ 2) P ∧
        (∫ ω, (M t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) ∧
      (∀ t ω,
        (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω) =
          x + ((t : ℝ) * X.c + M t ω + Jsmall t ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) -
            rightLimit D t ω) ∧
        (riskProcess X x D t ω =
          (x + ((t : ℝ) * X.c + M t ω + Jsmall t ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) -
            rightLimit D t ω) +
            (rightLimit D t ω - D t ω))) := by
  classical
  obtain ⟨M, hpath, hMeq, hMint, hMmart, hMbracket⟩ :=
    avram_jb19_original_gaussian_source_totalised_martingale_bracket
      X R Jsmall hRsource hJsource hRint hRmart hRbracket
  refine ⟨M, hpath, hMeq, ?_, hMint, hMmart, hMbracket, ?_⟩
  · intro t
    have ht : M t =ᵐ[P] R t := hMeq.mono (fun ω hω => hω t)
    exact (hRadapt t).congr ht.symm
  · intro t ω
    obtain ⟨hpost, hpre⟩ :=
      avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
        X x D hD ω t
    constructor
    · calc
        riskProcess X x D t ω -
            (rightLimit D t ω - D t ω) =
            x + X.X t ω - rightLimit D t ω := hpost
        _ = x + ((t : ℝ) * X.c + M t ω + Jsmall t ω +
              avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) -
              rightLimit D t ω := by rw [hpath t ω]
    · calc
        riskProcess X x D t ω =
            (x + X.X t ω - rightLimit D t ω) +
              (rightLimit D t ω - D t ω) := hpre
        _ = (x + ((t : ℝ) * X.c + M t ω + Jsmall t ω +
              avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) -
              rightLimit D t ω) +
              (rightLimit D t ω - D t ω) := by rw [hpath t ω]
