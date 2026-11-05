-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_integrable_of_locally_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:58:48.66771+00:00
-- url     : https://prove2.me/submissions/4325dcfc-b347-4c2b-9c77-9dba249a5e32

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_support_separated
import Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_continuous_compact_test_integrable_on_finite_negative_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal

/-- Local finite negative-band intensity integrates all compact negative tests. -/
theorem solution
    (μ : Measure ℝ)
    (hμ : ∀ ε : ℝ, 0 < ε → μ (Iic (-ε)) < ⊤)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    Integrable g μ := by
  obtain ⟨ε, hε, hsupport⟩ :=
    avram_p2_a_zero_rate_compact_negative_test_support_separated
      g hg hc hneg
  exact avram_p2_g_radon_continuous_compact_test_integrable_on_finite_negative_band
    μ g hg hc (hμ ε hε) hsupport
