-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_stopped_smallband_l1_limit_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:41:49.679047+00:00
-- url     : https://prove2.me/submissions/03eeeeeb-28b0-422f-9186-e963c4e1df6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_stopped_grid_l2_from_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
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
    (Ms : Ω → ℝ) (hMsI : Integrable Ms P)
    (hL1 : Tendsto (fun n =>
      ∫⁻ ω, ‖(∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) *
          ((N i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C i)).toReal)) - Ms ω‖ₑ ∂P)
      atTop (nhds 0)) :
    Integrable Ms P ∧ (∫ ω, Ms ω ∂P) = 0 := by
  refine ⟨hMsI, ?_⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ Finset.range n,
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)
  have hF : ∀ n, Integrable (F n) P ∧ (∫ ω, F n ω ∂P) = 0 := by
    intro n
    exact avram_p4_f_assembly_original_rightcont_stopped_grid_l2_from_predictable
      X τ hτstop grid hGrid ε hε C hC hBand hν N hActual H
      hH hHL2 hCountL2 n
  have hL1' : Tendsto (fun n => ∫⁻ ω, ‖F n ω - Ms ω‖ₑ ∂P)
      atTop (nhds 0) := by simpa [F] using hL1
  exact avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
    P F Ms hMsI.aestronglyMeasurable
    (fun n => (hF n).1) (fun n => (hF n).2) hL1'