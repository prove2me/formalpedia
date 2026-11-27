-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_eligible_measure_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:21:12.126557+00:00
-- url     : https://prove2.me/submissions/31f3f6fc-c5f5-419f-acff-1b81b0267216

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_restrict_atoms_diffuse_exact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0) :
    let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    let μ := (dividendMeasure D ω).restrict S
    IsFiniteMeasure μ := by 
  dsimp only
  obtain ⟨A, ma, md, _, _, _, _, _, _, _, hmass⟩ :=
    avram_p4_d_dividend_original_closed_stieltjes_restrict_atoms_diffuse_exact D hD ω H
  have hs : paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ) ⊆ Icc (0 : ℝ) (H : ℝ) :=
    fun t ht => ⟨ht.1.1, ht.2⟩
  refine ⟨lt_of_le_of_lt (Measure.restrict_mono_set _ hs univ) ?_⟩
  rw [hmass]
  exact ENNReal.ofReal_lt_top
