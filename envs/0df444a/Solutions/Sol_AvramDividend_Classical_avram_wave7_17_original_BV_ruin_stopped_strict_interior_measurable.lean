-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:31:44.401003+00:00
-- url     : https://prove2.me/submissions/5deacb94-cf5c-4d46-83e8-741e9bb4d55b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual left-limit controlled reserve defines a measurable ruin-stopped,
strictly positive, strictly sub-cap physical-time region. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (C : ℝ≥0∞) :
    MeasurableSet
      {p : ℝ≥0 × Ω |
        p.1 ≤ T ∧
        (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C} := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t
  have hpred : IsStronglyPredictable 𝓕.rightCont Y :=
    avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable X x D hD
  have hprogressive : IsStronglyProgressive 𝓕.rightCont Y :=
    hpred.isStronglyProgressive
  have hlocal : Measurable (fun p : Iic T × Ω => Y p.1.1 p.2) := by
    have hle :
        (Subtype.instMeasurableSpace.prod (𝓕.rightCont T)) ≤
          (inferInstance : MeasurableSpace (Iic T × Ω)) := by
      change (inferInstance : MeasurableSpace (Iic T)).prod (𝓕.rightCont T) ≤
        (inferInstance : MeasurableSpace (Iic T)).prod mΩ
      unfold MeasurableSpace.prod
      exact sup_le_sup (MeasurableSpace.comap_mono le_rfl)
        (MeasurableSpace.comap_mono ((𝓕.rightCont).le T))
    exact ((hprogressive T).measurable).mono hle le_rfl
  let s : Set (ℝ≥0 × Ω) := {p | p.1 ≤ T}
  have hs : MeasurableSet s := by
    exact measurableSet_le measurable_fst measurable_const
  let ψ : s → Iic T × Ω := fun p =>
    (⟨p.1.1, p.2⟩, p.1.2)
  have hfst : Measurable (fun p : s => p.1.1) :=
    measurable_fst.comp measurable_subtype_coe
  have hsnd : Measurable (fun p : s => p.1.2) :=
    measurable_snd.comp measurable_subtype_coe
  have hψ : Measurable ψ := by
    apply Measurable.prodMk
    · exact Measurable.subtype_mk hfst
    · exact hsnd
  have hY : Measurable (fun p : s => Y p.1.1 p.1.2) := by
    exact hlocal.comp hψ
  have hruin : Measurable (fun p : s => ruinTime X x D p.1.2) :=
    (ruinTime_measurable X x D hD).comp hsnd
  have htime : Measurable (fun p : s => (p.1.1 : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp hfst
  let u : Set s :=
    {p | (p.1.1 : ℝ≥0∞) < ruinTime X x D p.1.2 ∧
      0 < Y p.1.1 p.1.2 ∧ ENNReal.ofReal (Y p.1.1 p.1.2) < C}
  have hu : MeasurableSet u := by
    exact (measurableSet_lt htime hruin).inter
      ((measurableSet_lt measurable_const hY).inter
        (measurableSet_lt hY.ennreal_ofReal measurable_const))
  have himage : MeasurableSet (((↑) : s → ℝ≥0 × Ω) '' u) :=
    hs.subtype_image hu
  convert himage using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_prop, s, u, Y]
  aesop
