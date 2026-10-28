-- Prove2me | solution 1 for AvramDividend.Classical.chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:53:46.394528+00:00
-- url     : https://prove2.me/submissions/cbdebb6c-8017-4f04-b2e0-8cb4f4ca3203

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_mixed_borel_event_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) :
    (P.prod (expMeasure r)).map
      (fun z : Ω × ℝ =>
        (runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1,
         X.X z.2.toNNReal z.1 - X.X 0 z.1)) =
    (P.prod (expMeasure r)).map
      (fun z : Ω × ℝ =>
        (X.X 0 z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1},
         X.X z.2.toNNReal z.1 - X.X 0 z.1)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  letI : IsProbabilityMeasure (expMeasure r) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hr
  let μ : Measure (Ω × ℝ) := P.prod (expMeasure r)
  let T : Ω × ℝ → ℝ := fun z => X.X z.2.toNNReal z.1
  let Z : Ω × ℝ → ℝ := fun z => T z - X.X 0 z.1
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1 - T z
  let L : Ω × ℝ → ℝ := fun z =>
    X.X 0 z.1 +
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  let mD : Measure (ℝ × ℝ) := μ.map (fun z => (D z, Z z))
  let mL : Measure (ℝ × ℝ) := μ.map (fun z => (L z, Z z))
  have hTri := levy_exponential_real_clock_extrema_drawdown_measurable X
  have hD : Measurable D := by simpa only [D, T] using hTri.snd
  have hX0 : Measurable (fun z : Ω × ℝ => X.X 0 z.1) :=
    (X.adapted.measurable).comp measurable_fst
  have hL : Measurable L := hX0.add (by simpa only [] using hTri.fst.snd)
  have hT : Measurable T :=
    (chat04_levy_joint_time_state_measurable X).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hZ : Measurable Z := hT.sub hX0
  have hmD : Measurable (fun z : Ω × ℝ => (D z, Z z)) := hD.prodMk hZ
  have hmL : Measurable (fun z : Ω × ℝ => (L z, Z z)) := hL.prodMk hZ
  have hRay (A : Set ℝ) (hA : MeasurableSet A) (c : ℝ) :
      mD (A ×ˢ Iio c) = mL (A ×ˢ Iio c) := by
    rw [Measure.map_apply hmD (hA.prod measurableSet_Iio),
      Measure.map_apply hmL (hA.prod measurableSet_Iio)]
    simpa only [Set.preimage, Set.mem_prod, Set.mem_Iio,
      Set.mem_setOf_eq, D, L, Z, T] using
      (chat04_actual_exponential_clock_mixed_borel_event_reversal_ws01a
        X r hr c A hA)
  have hTotal (A : Set ℝ) (hA : MeasurableSet A) :
      mD (A ×ˢ Set.univ) = mL (A ×ˢ Set.univ) := by
    let F : ℕ → Set (ℝ × ℝ) := fun n => A ×ˢ Iio (n : ℝ)
    have hm : Monotone F := by
      intro i j hij z hz
      change z.1 ∈ A ∧ z.2 < (i : ℝ) at hz
      change z.1 ∈ A ∧ z.2 < (j : ℝ)
      have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      exact ⟨hz.1, lt_of_lt_of_le hz.2 hijR⟩
    have hCover : (⋃ n, F n) = A ×ˢ Set.univ := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_Iio,
        Set.mem_univ, and_true, F]
      constructor
      · rintro ⟨n, ha, _⟩
        exact ha
      · intro ha
        obtain ⟨n, hn⟩ := exists_nat_gt z.2
        exact ⟨n, ha, hn⟩
    rw [← hCover, hm.measure_iUnion, hm.measure_iUnion]
    exact iSup_congr (fun n => hRay A hA (n : ℝ))
  have hRect (A B : Set ℝ) (hA : MeasurableSet A)
      (hB : MeasurableSet B) :
      mD (A ×ˢ B) = mL (A ×ˢ B) := by
    let nD : Measure ℝ := (mD.restrict (A ×ˢ Set.univ)).map Prod.snd
    let nL : Measure ℝ := (mL.restrict (A ×ˢ Set.univ)).map Prod.snd
    have hSection (M : Measure (ℝ × ℝ)) (B : Set ℝ)
        (hB : MeasurableSet B) :
        ((M.restrict (A ×ˢ Set.univ)).map Prod.snd) B =
          M (A ×ˢ B) := by
      rw [Measure.map_apply measurable_snd hB,
        Measure.restrict_apply (hB.preimage measurable_snd)]
      congr 1
      ext z
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
        Set.mem_univ, and_true, Set.mem_setOf_eq]
      exact and_comm
    have hnIio (c : ℝ) : nD (Iio c) = nL (Iio c) := by
      rw [hSection mD (Iio c) measurableSet_Iio,
        hSection mL (Iio c) measurableSet_Iio]
      exact hRay A hA c
    have hnTotal : nD Set.univ = nL Set.univ := by
      rw [hSection mD Set.univ MeasurableSet.univ,
        hSection mL Set.univ MeasurableSet.univ]
      exact hTotal A hA
    have hnEq : nD = nL := by
      apply Measure.ext_of_Ici
      intro c
      have h1 : nD (Ici c) = nD Set.univ - nD (Iio c) := by
        simpa only [Set.compl_Iio] using
          (measure_compl (μ := nD) measurableSet_Iio
            (measure_ne_top nD (Iio c)))
      have h2 : nL (Ici c) = nL Set.univ - nL (Iio c) := by
        simpa only [Set.compl_Iio] using
          (measure_compl (μ := nL) measurableSet_Iio
            (measure_ne_top nL (Iio c)))
      rw [h1, h2, hnTotal, hnIio c]
    have h := congrArg (fun M : Measure ℝ => M B) hnEq
    change ((mD.restrict (A ×ˢ Set.univ)).map Prod.snd) B =
      ((mL.restrict (A ×ˢ Set.univ)).map Prod.snd) B at h
    rw [hSection mD B hB, hSection mL B hB] at h
    exact h
  have heq : mD = mL := by
    apply Measure.ext_prod
    intro A B hA hB
    exact hRect A B hA hB
  exact heq
