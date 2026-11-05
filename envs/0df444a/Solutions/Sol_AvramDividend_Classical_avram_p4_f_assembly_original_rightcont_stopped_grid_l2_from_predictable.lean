-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_rightcont_stopped_grid_l2_from_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:05:22.582412+00:00
-- url     : https://prove2.me/submissions/006dad19-47ea-4c3d-9a07-6340e4bf7f8d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_stopped_grid_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (C i) < ⊤)
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
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) 2 P)
    (n : ℕ) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range n, (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0) then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0) then (0 : ℝ) else H i ω) *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by
  have hMeas : ∀ i, Measurable (N i) := by
    intro i
    rw [hActual i]
    exact avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X (grid i) (grid (i + 1)) (hGrid i) (C i) (hC i)
  have hMaskedL2 : ∀ i, MemLp (fun ω =>
      if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
      then (0 : ℝ) else H i ω) 2 P := by
    intro i
    have hStopMeas : MeasurableSet
        {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)} :=
      (MeasurableSpace.le_def.mp (𝓕.rightCont.le (grid i))) _
        (hτstop (grid i))
    have hContinueMeas : MeasurableSet
        {ω : Ω | ¬ (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)} := by
      simpa only [Set.compl_setOf] using hStopMeas.compl
    have hIndicator : MemLp
        (({ω : Ω | ¬ (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)}).indicator
          (H i)) 2 P :=
      MeasureTheory.MemLp.indicator hContinueMeas (hHL2 i)
    convert hIndicator using 1
    ext ω
    rw [Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
    by_cases h : (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
    · simp only [if_pos h, if_neg (not_not.mpr h)]
    · simp only [if_neg h, if_pos h]
  exact avram_p4_f_assembly_original_rightcont_stopped_grid_zero_mean
    X τ hτstop grid hGrid ε hε C hC hBand hν
    N hActual hMeas H hH hMaskedL2 hCountL2 n
