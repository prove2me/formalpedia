-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_ruin_graph_finite_pushed_clock_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:43:53.446184+00:00
-- url     : https://prove2.me/submissions/de6fbb93-c871-4f34-a3fd-709775cd202c

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

/-- The actual ruin graph is null under the physical finite-horizon clock
pushed from real Lebesgue time to nonnegative time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    let νT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    (P.prod νT)
      {p : Ω × ℝ≥0 |
        (p.2 : ℝ≥0∞) = ruinTime X x D p.1} = 0 := by
  let νT : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  let s : Set (Ω × ℝ≥0) :=
    {p | (p.2 : ℝ≥0∞) = ruinTime X x D p.1}
  have hτ : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD
  have hs : MeasurableSet s :=
    measurableSet_eq_fun
      (measurable_coe_nnreal_ennreal.comp measurable_snd)
      (hτ.comp measurable_fst)
  have htm : Measurable Real.toNNReal := by fun_prop
  have hSec : ∀ ω : Ω, νT (Prod.mk ω ⁻¹' s) = 0 := by
    intro ω
    let A : Set ℝ≥0 := Prod.mk ω ⁻¹' s
    have hAm : MeasurableSet A := by
      change MeasurableSet {t : ℝ≥0 |
        (t : ℝ≥0∞) = ruinTime X x D ω}
      exact measurableSet_eq_fun
        measurable_coe_nnreal_ennreal measurable_const
    have hsub : ((Real.toNNReal ⁻¹' A) ∩
        Icc (0 : ℝ) (T : ℝ)).Subsingleton := by
      intro u hu v hv
      have hu0 : 0 ≤ u := hu.2.1
      have hv0 : 0 ≤ v := hv.2.1
      have huA : (u.toNNReal : ℝ≥0∞) =
          ruinTime X x D ω := hu.1
      have hvA : (v.toNNReal : ℝ≥0∞) =
          ruinTime X x D ω := hv.1
      have hNN : u.toNNReal = v.toNNReal :=
        ENNReal.coe_inj.mp (huA.trans hvA.symm)
      calc
        u = (u.toNNReal : ℝ) := (Real.coe_toNNReal u hu0).symm
        _ = (v.toNNReal : ℝ) := congrArg Subtype.val hNN
        _ = v := Real.coe_toNNReal v hv0
    have hAreal :
        ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ)))
          (Real.toNNReal ⁻¹' A) = 0 := by
      rw [Measure.restrict_apply' measurableSet_Icc]
      exact hsub.measure_zero _
    change νT A = 0
    rw [Measure.map_apply htm hAm]
    exact hAreal
  have hae :
      (fun ω : Ω => νT (Prod.mk ω ⁻¹' s))
        =ᵐ[P] (fun _ => (0 : ℝ≥0∞)) := by
    filter_upwards [] with ω
    exact hSec ω
  exact Measure.measure_prod_null_of_ae_null hs hae
