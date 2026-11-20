-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_NX_discounted_negative_JL_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:06:29.725041+00:00
-- url     : https://prove2.me/submissions/cb251583-70bf-4bbf-a919-1b49320cdec5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_NX_ae_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (η : ℝ) (hη : 0 < η) (hηone : η < 1)
    (a S d : ℝ≥0 × ℝ → ℝ)
    (hH : Integrable (fun p => a p *
      (S p - (if -1 < p.2 then p.2 * d p else 0)))
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧
        X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s))))
    (hL : Integrable (fun p =>
      if p.2 ∈ Ioo (-1 : ℝ) (-η) then a p * p.2 * d p else 0)
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧
        X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))) :
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧
        X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    (∫ p, a p * (S p - (if -1 < p.2 then p.2 * d p else 0)) ∂NX) +
    (∫ p, (if p.2 ∈ Ioo (-1 : ℝ) (-η) then
      a p * p.2 * d p else 0) ∂NX) =
    ∫ p, a p * (S p - (if -η ≤ p.2 then p.2 * d p else 0)) ∂NX := by
  dsimp
  rw [← integral_add hH hL]
  apply integral_congr_ae
  filter_upwards
    [AvramDividend.Classical.avram_pj_workerC_original_NX_ae_negative_jumps
      X ω] with p hp
  have hbase :=
    AvramDividend.Classical.avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
      η p.2 (S p) (d p) hη hηone hp
  by_cases hcut : p.2 ∈ Ioo (-1 : ℝ) (-η)
  · simp only [hcut, if_true]
    calc
      a p * (S p - (if -1 < p.2 then p.2 * d p else 0)) +
        a p * p.2 * d p =
        a p * ((S p - (if -1 < p.2 then p.2 * d p else 0)) +
          p.2 * d p) := by ring
      _ = _ := by
        have hbase' :
            (S p - (if -1 < p.2 then p.2 * d p else 0)) +
              p.2 * d p =
            S p - (if -η ≤ p.2 then p.2 * d p else 0) := by
          simpa only [hcut, if_true] using hbase
        exact congrArg (fun y : ℝ => a p * y) hbase' 
  · simp only [hcut, if_false, add_zero]
    have heq : S p - (if -1 < p.2 then p.2 * d p else 0) =
      S p - (if -η ≤ p.2 then p.2 * d p else 0) := by
        simpa [hcut] using hbase
    rw [heq]

