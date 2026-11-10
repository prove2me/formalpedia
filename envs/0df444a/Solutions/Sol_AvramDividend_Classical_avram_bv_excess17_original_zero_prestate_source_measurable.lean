-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess17_original_zero_prestate_source_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T19:13:02.54329+00:00
-- url     : https://prove2.me/submissions/351c1331-1c39-46f3-870f-47a23c968779

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s : ℝ≥0) :
    MeasurableSet[𝓕.rightCont s] {ω : Ω |
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) s = 0} := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    x + X.X t ω - rightLimit D t ω
  have hAdapt : StronglyAdapted 𝓕.rightCont Z :=
    avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont X x D hD
  have hLeft : ∀ ω (t : ℝ≥0), 0 < t →
      ∃ l : ℝ, Tendsto (fun u => Z u ω) (𝓝[<] t) (𝓝 l) := by
    intro ω t ht
    obtain ⟨l, hl, _⟩ :=
      avram_wave3_04_postPaymentReserve_prejump_upper X x D hD ω t ht
    exact ⟨l, hl⟩
  have hZ : StronglyAdapted 𝓕.rightCont
      (fun t ω => Function.leftLim (fun u => Z u ω) t) :=
    avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits Z hAdapt hLeft
  exact (measurableSet_singleton (0 : ℝ)).preimage (hZ s).measurable
