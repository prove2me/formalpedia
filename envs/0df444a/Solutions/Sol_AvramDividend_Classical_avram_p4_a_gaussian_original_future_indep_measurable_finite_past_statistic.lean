-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_future_indep_measurable_finite_past_statistic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:37:33.974091+00:00
-- url     : https://prove2.me/submissions/db711300-26af-4b13-a356-d6d3df16da2f

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_finite_past_vector

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≤ s)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Measurable φ) :
    IndepFun
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
      (fun ω => φ (fun i : Fin n => Y.X (v i) ω)) P := by
  have hvec : IndepFun
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
      (fun ω => fun i : Fin n => Y.X (v i) ω) P :=
    avram_p4_a_gaussian_original_centred_increment_indep_finite_past_vector
      Y s t hst n v hv
  exact hvec.comp measurable_id hφ
