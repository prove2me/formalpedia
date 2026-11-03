-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_real_clock_ruin_graph_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:51:49.73216+00:00
-- url     : https://prove2.me/submissions/93d693f5-9215-4a22-b89b-1d2d7e36733e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual ruin stopping graph is null under original P times physical
real Lebesgue time, without discarding a Stieltjes or source-jump atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    (P.prod (volume : Measure ℝ))
      {p : Ω × ℝ |
        0 ≤ p.2 ∧ ENNReal.ofReal p.2 = ruinTime X x D p.1} = 0 := by
  let s : Set (Ω × ℝ) :=
    {p | 0 ≤ p.2 ∧ ENNReal.ofReal p.2 = ruinTime X x D p.1}
  have hτ : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD
  have hs : MeasurableSet s := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_eq_fun measurable_snd.ennreal_ofReal
        (hτ.comp measurable_fst))
  have hSec : ∀ ω : Ω,
      (volume : Measure ℝ) (Prod.mk ω ⁻¹' s) = 0 := by
    intro ω
    apply Set.Subsingleton.measure_zero
    intro u hu v hv
    have hu0 : 0 ≤ u := hu.1
    have hv0 : 0 ≤ v := hv.1
    have heq : ENNReal.ofReal u = ENNReal.ofReal v :=
      hu.2.trans hv.2.symm
    have hre := congrArg ENNReal.toReal heq
    simpa only [ENNReal.toReal_ofReal hu0,
      ENNReal.toReal_ofReal hv0] using hre
  have hae :
      (fun ω : Ω => (volume : Measure ℝ) (Prod.mk ω ⁻¹' s))
        =ᵐ[P] (fun _ => (0 : ℝ≥0∞)) := by
    filter_upwards [] with ω
    exact hSec ω
  exact Measure.measure_prod_null_of_ae_null hs hae
