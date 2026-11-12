-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_single_random_mark_interval_product_law_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:47:40.866314+00:00
-- url     : https://prove2.me/submissions/0fb90c94-02dd-4ca5-9b63-070ca748f374

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_independent_pair_measurable_image_law_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_measurable_random_mark_interval_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- The random marked-interval law is the independent product-law image. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (i : Fin n) :
    Measure.map (fun ω : Ω =>
      ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P =
    Measure.map (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j)
      ((Measure.map (fun ω => fun k => N k ω) P).prod
        (Measure.map (fun ω => fun k => Y k ω) P)) := by
  apply AvramDividend.Classical.avram_a06_independent_pair_measurable_image_law_20261111
    P (fun ω => fun k => N k ω) (fun ω => fun k => Y k ω)
    (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j)
    hN hY ?_ hSeparate
  exact AvramDividend.Classical.avram_a06_measurable_random_mark_interval_20261111
    (fun (p : (Fin (n + 1) → ℕ) × (ℕ → ℝ)) => p.1 i.castSucc) (fun (p : (Fin (n + 1) → ℕ) × (ℕ → ℝ)) => p.1 i.succ)
    (fun j (p : (Fin (n + 1) → ℕ) × (ℕ → ℝ)) => p.2 j)
    ((measurable_pi_apply i.castSucc).comp measurable_fst)
    ((measurable_pi_apply i.succ).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp measurable_snd)