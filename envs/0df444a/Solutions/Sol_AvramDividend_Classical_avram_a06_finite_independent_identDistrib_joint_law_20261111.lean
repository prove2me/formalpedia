-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_finite_independent_identDistrib_joint_law_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:12:56.837502+00:00
-- url     : https://prove2.me/submissions/d90a1dae-7ea7-44a3-9dc7-d9b0fd462a89

import Mathlib.Probability.IdentDistrib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- Matching independent marginal laws determine the full finite joint law. -/
theorem solution
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (U V : Fin n → Ω → A)
    (hU : ∀ i, Measurable (U i)) (hV : ∀ i, Measurable (V i))
    (hIndU : iIndepFun U P) (hIndV : iIndepFun V P)
    (hLaw : ∀ i, IdentDistrib (U i) (V i) P P) :
    IdentDistrib (fun ω => fun i : Fin n => U i ω)
      (fun ω => fun i : Fin n => V i ω) P P := by
  have hMU : Measurable (fun ω => fun i : Fin n => U i ω) :=
    measurable_pi_iff.mpr hU
  have hMV : Measurable (fun ω => fun i : Fin n => V i ω) :=
    measurable_pi_iff.mpr hV
  refine ⟨hMU.aemeasurable, hMV.aemeasurable, ?_⟩
  rw [ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
    (fun i => (hU i).aemeasurable) hIndU]
  rw [ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
    (fun i => (hV i).aemeasurable) hIndV]
  congr 1
  funext i
  exact (hLaw i).map_eq
