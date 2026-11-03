-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:47:22.185202+00:00
-- url     : https://prove2.me/submissions/22460927-161e-4d34-badf-6dbe194cc567

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual pre-payment reserve has a jointly measurable finite-horizon
truncation on the original physical time and original probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × Ω =>
      if p.1 ≤ T then
        Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1
      else 0) := by
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
  have hs : MeasurableSet s :=
    measurableSet_le measurable_fst measurable_const
  let ψ : s → Iic T × Ω := fun p => (⟨p.1.1, p.2⟩, p.1.2)
  have hfst : Measurable (fun p : s => p.1.1) :=
    measurable_fst.comp measurable_subtype_coe
  have hsnd : Measurable (fun p : s => p.1.2) :=
    measurable_snd.comp measurable_subtype_coe
  have hψ : Measurable ψ := by
    apply Measurable.prodMk
    · exact Measurable.subtype_mk hfst
    · exact hsnd
  have hin : Measurable (fun p : s =>
      if p.1.1 ≤ T then Y p.1.1 p.1.2 else 0) := by
    have hinY : Measurable (fun p : s => Y p.1.1 p.1.2) :=
      hlocal.comp hψ
    convert hinY using 1
    funext p
    have ht : p.1.1 ≤ T := p.property
    simp only [if_pos ht]
  let r : Set (ℝ≥0 × Ω) := {p | ¬ p.1 ≤ T}
  have hr : MeasurableSet r := hs.compl
  have hout : Measurable (fun p : r =>
      if p.1.1 ≤ T then Y p.1.1 p.1.2 else 0) := by
    convert (measurable_const : Measurable (fun _ : r => (0 : ℝ))) using 1
    funext p
    have hp : ¬ p.1.1 ≤ T := p.2
    simp only [if_neg hp]
  have hcover : (Set.univ : Set (ℝ≥0 × Ω)) ⊆ s ∪ r := by
    intro p hp
    by_cases h : p ∈ s
    · exact Or.inl h
    · exact Or.inr h
  have hfull : Measurable (fun p : ℝ≥0 × Ω =>
      if p.1 ≤ T then Y p.1 p.2 else 0) := by
    apply measurable_of_measurable_union_cover s r hs hr hcover
    · exact hin
    · exact hout
  simpa only [Y] using hfull
