-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys127_original_finite_horizon_prepayment_eq_risk_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:56:52.470193+00:00
-- url     : https://prove2.me/submissions/bda7eb9f-44b1-4af8-8a48-c1ba16170ad8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys116_original_admissible_dividend_ae_continuity
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- On the original event of a source-free stopped finite horizon,
the physical prepayment left limit equals risk almost everywhere. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (ω : Ω) (S : ℝ≥0)
    (hsource : ∀ s : ℝ≥0, s ≤ S → X.X s ω = (s : ℝ) * X.drift) :
    ∀ᵐ t ∂μ, 0 < (t : ℝ≥0) → t ≤ S →
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t =
          riskProcess X x D t ω := by
  have hzero :=
    avram_bvb_phys116_original_admissible_dividend_ae_continuity
      X x C D hD μ ω
  have hae : ∀ᵐ t ∂μ, ContinuousAt (fun s : ℝ≥0 => D s ω) t := by
    simpa only [Set.mem_setOf_eq, not_not] using
      (measure_eq_zero_iff_ae_notMem.mp hzero)
  filter_upwards [hae] with t ht htpos htS
  have hnb : (nhdsWithin t (Iio t)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  rw [avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
    X x C D hD ω S t htS hnb hsource]
  rw [ht.continuousWithinAt.leftLim_eq]
  simp only [riskProcess, hsource t htS]
