-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_any_intrinsic_gaussian_limit_L1_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:10:33.931074+00:00
-- url     : https://prove2.me/submissions/49d9a8c3-c38e-4f99-8766-dfc0998a98de

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Intrinsic Gaussian source martingality is invariant under almost-everywhere choice of source limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    (∀ t : ℝ≥0, Integrable (R t) P) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω) := by
  obtain ⟨S, hS, _, hSint, hSmart⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists X hX hFinite
  have hRS : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, R t ω = S t ω := by
    filter_upwards [hRsource, hS] with ω hωR hωS
    intro t
    exact tendsto_nhds_unique (hωR t) (hωS.1 t)
  constructor
  · intro t
    exact (hSint t).congr (by filter_upwards [hRS] with ω hh; exact (hh t).symm)
  · intro s t hst
    have hEq : R t =ᵐ[P] S t := by
      filter_upwards [hRS] with ω hh
      exact hh t
    have hCond := condExp_congr_ae (m := 𝓕.rightCont s) hEq
    filter_upwards [hCond, hSmart s t hst, hRS] with ω h1 h2 h3
    rw [h1, h2, h3 s]
