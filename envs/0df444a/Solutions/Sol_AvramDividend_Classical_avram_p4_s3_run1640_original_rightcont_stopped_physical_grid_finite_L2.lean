-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1640_original_rightcont_stopped_physical_grid_finite_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:11:54.146952+00:00
-- url     : https://prove2.me/submissions/a63b9dc7-c157-43c4-8e46-aa1ce847aa31

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_g_original_rightcont_same_window_mark_simple_L2_martingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Every finite original ruin-stopped compensated negative-jump grid is L². -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, C i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ) :
    MemLp (fun ω =>
      ∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) *
          ((N i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C i)).toReal)) 2 P := by
  classical
  let W : ℕ → Ω → ℝ := fun i ω =>
    (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
      then (0 : ℝ) else H i ω)
  let Z : ℕ → Ω → ℝ := fun i ω =>
    W i ω * ((N i ω).toReal -
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (C i)).toReal)
  change MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P
  have hW (i : ℕ) :
      StronglyMeasurable[𝓕.rightCont (grid i)] (W i) ∧
      MemLp (W i) 2 P ∧ (∀ ω, |W i ω| ≤ L) := by
    have hStop : MeasurableSet[𝓕.rightCont (grid i)]
        {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)} :=
      hτstop (grid i)
    have hSM : StronglyMeasurable[𝓕.rightCont (grid i)] (W i) :=
      StronglyMeasurable.ite hStop stronglyMeasurable_const (hH i)
    have hContinue : MeasurableSet
        {ω : Ω | ¬ (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)} := by
      have hAmbient : MeasurableSet
          {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)} :=
        (MeasurableSpace.le_def.mp (𝓕.rightCont.le (grid i))) _ hStop
      simpa only [Set.compl_setOf] using hAmbient.compl
    have hIndicator : MemLp
        (({ω : Ω | ¬ (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)}).indicator
          (H i)) 2 P :=
      MeasureTheory.MemLp.indicator hContinue (hHL2 i)
    have hLp : MemLp (W i) 2 P := by
      convert hIndicator using 1
      ext ω
      rw [Set.indicator_apply]
      simp only [Set.mem_setOf_eq]
      by_cases h : (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
      · simp only [W, if_pos h, if_neg (not_not.mpr h)]
      · simp only [W, if_neg h, if_pos h]
    have hB (ω : Ω) : |W i ω| ≤ L := by
      by_cases hs : (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
      · simpa only [W, if_pos hs, abs_zero] using
          (abs_nonneg (H i ω)).trans (hBound i ω)
      · simpa only [W, if_neg hs] using hBound i ω
    exact ⟨hSM, hLp, hB⟩
  have hCell (i : ℕ) : MemLp (Z i) 2 P := by
    have hOne :=
      avram_p4_s3_interval_g_original_rightcont_same_window_mark_simple_L2_martingale
        X T cut (grid i) (grid (i + 1)) (hGrid i) (hTime (i + 1))
          ε hε (fun _ : Unit => C i)
          (by intro _; exact hC i)
          (by intro _; exact hBand i)
          (by intro _; exact hCut i)
          (fun _ : Unit => W i)
          (by intro _; exact (hW i).1)
          (by intro _; exact (hW i).2.1)
          L (by intro _ ω; exact (hW i).2.2 ω)
          ({()} : Finset Unit)
    change MemLp (fun ω => W i ω *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (C i)).toReal)) 2 P
    rw [hActual i]
    simpa only [Finset.sum_singleton, Finset.sum_apply] using hOne.1
  have hSum (S : Finset ℕ) : MemLp (∑ i ∈ S, Z i) 2 P := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a R ha ih =>
      simpa only [Finset.sum_insert ha] using (hCell a).add ih
  have hPointwise : (∑ i ∈ Finset.range n, Z i) =
      (fun ω => ∑ i ∈ Finset.range n, Z i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [← hPointwise]
  exact hSum (Finset.range n)
