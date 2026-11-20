-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_compensated_two_measure_JL_negative_mark_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:03:21.545193+00:00
-- url     : https://prove2.me/submissions/4c3a38be-c276-420e-b467-649041bf8567

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (M N : Measure (ℝ≥0 × ℝ)) (η : ℝ)
    (S d : (ℝ≥0 × ℝ) → ℝ)
    (hη : 0 < η) (hηone : η < 1)
    (hMneg : ∀ᵐ p ∂M, p.2 < 0)
    (hNneg : ∀ᵐ p ∂N, p.2 < 0)
    (hHM : Integrable (fun p => S p -
      (if -1 < p.2 then p.2 * d p else 0)) M)
    (hLM : Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0) M)
    (hHN : Integrable (fun p => S p -
      (if -1 < p.2 then p.2 * d p else 0)) N)
    (hLN : Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0) N) :
    ((∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂M) -
      (∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂N)) +
    ((∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂M) -
      (∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂N)) =
    (∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂M) -
    (∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂N) := by
  have hM :
      (∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂M) +
      (∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂M) =
      ∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂M := by
    rw [← integral_add hHM hLM]
    apply integral_congr_ae
    filter_upwards [hMneg] with p hp
    exact
      AvramDividend.Classical.avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
        η p.2 (S p) (d p) hη hηone hp
  have hN :
      (∫ p, S p - (if -1 < p.2 then p.2 * d p else 0) ∂N) +
      (∫ p, if p.2 ∈ Ioo (-1 : ℝ) (-η) then p.2 * d p else 0 ∂N) =
      ∫ p, S p - (if -η ≤ p.2 then p.2 * d p else 0) ∂N := by
    rw [← integral_add hHN hLN]
    apply integral_congr_ae
    filter_upwards [hNneg] with p hp
    exact
      AvramDividend.Classical.avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
        η p.2 (S p) (d p) hη hηone hp
  rw [← hM, ← hN]
  ring

