-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_rightcont_stopped_finiteband_grid_L1_from_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:50:04.239458+00:00
-- url     : https://prove2.me/submissions/5d7aa736-5e4e-4844-bfd0-8daae5873976

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_stopped_grid_l2_from_predictable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
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
    (k : ℕ) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
         then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range k,
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
       then (0 : ℝ) else H i ω) *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by
  have hν : ∀ i, X.ν (C i) < ⊤ := by
    intro i
    have hSep : C i ⊆ Iic (-ε) := by
      intro z hz
      exact le_of_lt ((hBand i) hz).2
    exact avram_p2_a_zero_rate_separated_borel_nu_finite
      X (C i) (hC i) ε hε hSep
  have hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) 2 P := by
    intro i
    have hCell :=
      avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
        X T cut (grid i) (grid (i + 1)) (hGrid i)
        (hTime (i + 1)) (C i) (hC i) (hCut i)
    simpa only [hActual i] using hCell
  exact avram_p4_f_assembly_original_rightcont_stopped_grid_l2_from_predictable
    X τ hτstop grid hGrid ε hε C hC hBand hν
    N hActual H hH hHL2 hCountL2 k
