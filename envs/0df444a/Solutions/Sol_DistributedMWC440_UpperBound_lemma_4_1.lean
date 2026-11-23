-- Prove2me | solution 1 for DistributedMWC440.UpperBound.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:38:07.455795+00:00
-- url     : https://prove2.me/submissions/2f658b7e-64f2-437a-8c20-addd4a4edd26

import Definitions.Def_DistributedMWC440_UpperBound_Operations
import Theorems.Thm_ExpLaw_tail

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory
open DistributedMWC440.UpperBound
noncomputable section

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) (hS : 2 ≤ S.card) (k d : ℝ) (hk : 1/2 ≤ k) (hd : 0 < d) :
    shiftLaw S (rate S k d) {δ | ∀ s, trunc S k d δ s = δ s} =
      shiftLaw S (rate S k d) {δ | ∀ s, δ s ≤ deltaMax S k d} ∧
    ENNReal.ofReal (1 - Real.exp (-1) * (S.card : ℝ)^(-1/k)) ≤
      shiftLaw S (rate S k d) {δ | ∀ s, δ s ≤ deltaMax S k d} := by
  have hcard : (1 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS
  have hN : (0 : ℝ) < (S.card : ℝ) := by linarith
  have hlog : 0 < Real.log (S.card : ℝ) := Real.log_pos hcard
  have hk0 : 0 < k := by linarith
  have hr : 0 < rate S k d := div_pos hlog (mul_pos hk0 hd)
  letI : IsProbabilityMeasure (expMeasure (rate S k d)) :=
    isProbabilityMeasure_expMeasure hr
  letI : IsProbabilityMeasure (shiftLaw S (rate S k d)) := by
    unfold shiftLaw
    infer_instance
  have hM : 0 ≤ deltaMax S k d := by
    unfold deltaMax
    positivity
  let A : Set (Shifts S) := {δ | ∀ s, δ s ≤ deltaMax S k d}
  have hAeq : A = Set.univ.pi (fun _ : S => Set.Iic (deltaMax S k d)) := by
    ext δ
    simp [A, Pi.le_def]
  have hA : MeasurableSet A := by
    rw [hAeq]
    exact MeasurableSet.univ_pi (fun _ => measurableSet_Iic)
  have hAc : Aᶜ = ⋃ s : S, {δ : Shifts S | deltaMax S k d < δ s} := by
    ext δ
    simp [A, not_le]
  have htail : ∀ s : S,
      shiftLaw S (rate S k d) {δ : Shifts S | deltaMax S k d < δ s} ≤
        ENNReal.ofReal (Real.exp (-1) * (S.card : ℝ)^(-(1 + 1/k))) := by
    intro s
    have hcoord : (shiftLaw S (rate S k d)).map (fun δ => δ s) =
        expMeasure (rate S k d) := by
      unfold shiftLaw
      rw [Measure.pi_map_eval]
      simp [measure_univ]
    have hevent := Measure.map_apply
      (μ := shiftLaw S (rate S k d)) (f := fun δ : Shifts S => δ s)
      (measurable_pi_apply s)
      (measurableSet_Ici : MeasurableSet (Set.Ici (deltaMax S k d)))
    rw [hcoord] at hevent
    calc
      shiftLaw S (rate S k d) {δ : Shifts S | deltaMax S k d < δ s} ≤
          shiftLaw S (rate S k d) {δ : Shifts S | deltaMax S k d ≤ δ s} :=
        measure_mono (by
          intro δ hδ
          change deltaMax S k d < δ s at hδ
          change deltaMax S k d ≤ δ s
          exact hδ.le)
      _ = expMeasure (rate S k d) (Set.Ici (deltaMax S k d)) := hevent.symm
      _ = ENNReal.ofReal ((expMeasure (rate S k d) (Set.Ici (deltaMax S k d))).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = ENNReal.ofReal (Real.exp (-(rate S k d * deltaMax S k d))) := by
        rw [ExpLaw.tail hr hM]
      _ = ENNReal.ofReal (Real.exp (-1) * (S.card : ℝ)^(-(1 + 1/k))) := by
        congr 1
        have hβM : rate S k d * deltaMax S k d =
            (1 + 1/k) * Real.log (S.card : ℝ) + 1 := by
          unfold rate deltaMax
          field_simp [ne_of_gt hk0, ne_of_gt hd, ne_of_gt hlog]
          <;> ring
        rw [hβM, Real.rpow_def_of_pos hN]
        have he : -((1 + 1/k) * Real.log (S.card : ℝ) + 1) =
            -1 + Real.log (S.card : ℝ) * (-(1 + 1/k)) := by ring
        rw [he, Real.exp_add]
  have hpow : (S.card : ℝ) * (S.card : ℝ)^(-(1 + 1/k)) =
      (S.card : ℝ)^(-1/k) := by
    nth_rewrite 1 [← Real.rpow_one (S.card : ℝ)]
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hcomp : (shiftLaw S (rate S k d)) Aᶜ ≤
      ENNReal.ofReal (Real.exp (-1) * (S.card : ℝ)^(-1/k)) := by
    rw [hAc]
    calc
      (shiftLaw S (rate S k d)) (⋃ s : S, {δ : Shifts S | deltaMax S k d < δ s}) ≤
          ∑' s : S, (shiftLaw S (rate S k d)) {δ : Shifts S | deltaMax S k d < δ s} :=
        measure_iUnion_le _
      _ = ∑ s : S, (shiftLaw S (rate S k d)) {δ : Shifts S | deltaMax S k d < δ s} :=
        tsum_fintype _
      _ ≤ ∑ _s : S, ENNReal.ofReal
          (Real.exp (-1) * (S.card : ℝ)^(-(1 + 1/k))) := by
        exact Finset.sum_le_sum (fun s _ => htail s)
      _ = ENNReal.ofReal (Real.exp (-1) * (S.card : ℝ)^(-1/k)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]
          calc
            (S.card : ℝ) * (Real.exp (-1) * (S.card : ℝ)^(-(1 + 1/k))) =
                Real.exp (-1) * ((S.card : ℝ) * (S.card : ℝ)^(-(1 + 1/k))) := by ring
            _ = Real.exp (-1) * (S.card : ℝ)^(-1/k) := by rw [hpow]
        · intro s _
          positivity
  have hmain : ENNReal.ofReal (1 - Real.exp (-1) * (S.card : ℝ)^(-1/k)) ≤
      (shiftLaw S (rate S k d)) A := by
    have hq : 0 ≤ Real.exp (-1) * (S.card : ℝ)^(-1/k) := by positivity
    rw [ENNReal.ofReal_sub 1 hq, ENNReal.ofReal_one]
    have hAformula : (shiftLaw S (rate S k d)) A =
        1 - (shiftLaw S (rate S k d)) Aᶜ := by
      have hc := measure_compl hA (measure_ne_top (shiftLaw S (rate S k d)) A)
      rw [measure_univ] at hc
      rw [hc]
      have hAle : (shiftLaw S (rate S k d)) A ≤ 1 := by
        calc
          (shiftLaw S (rate S k d)) A ≤ (shiftLaw S (rate S k d)) Set.univ :=
            measure_mono (Set.subset_univ A)
          _ = 1 := measure_univ
      exact (ENNReal.sub_sub_cancel (by simp) hAle).symm
    rw [hAformula]
    exact tsub_le_tsub_left hcomp 1
  constructor
  · congr 1
    ext δ
    simp [trunc]
  · exact hmain
