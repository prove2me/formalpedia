-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_prepayment_leftLim_finite_horizon_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:10:41.469404+00:00
-- url     : https://prove2.me/submissions/3978aa85-c9d1-463d-a3ee-31f6ef437db0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_postpayment_upper_horizon_strip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Extend the proved post-payment horizon ceiling to every positive-time
left limit by the closedness of the upper real half-line. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      0 < t → (t : ℝ) ≤ T →
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤
        x + max (T * X.drift) 0 := by
  let R : ℝ≥0 := ⟨T, le_of_lt hT⟩
  have hglobal :=
    avram_bv_residual9_original_global_postpayment_upper_horizon_strip
      X hBV x D hD.1.1 R
  filter_upwards [hglobal] with ω hω
  intro t ht htT
  let H : ℝ := x + max (T * X.drift) 0
  let f : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
  have htR : t ≤ R := by
    change (t : ℝ) ≤ T
    exact htT
  have hbounded : ∀ s : ℝ≥0, s ≤ t → f s ∈ Iic H := by
    intro s hs
    exact hω s (hs.trans htR)
  have hmem : ∀ᶠ s in 𝓝[≤] t, f s ∈ Iic H := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbounded s hs
  have hz : f.leftLim t ≤ H :=
    isClosed_Iic.mem_of_mapClusterPt (mapClusterPt_leftLim f t) hmem
  exact hz
