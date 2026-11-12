-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_independent_stream_integral_disintegration_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:04:00.29909+00:00
-- url     : https://prove2.me/submissions/8fabac5f-25a6-4b53-a9d2-ac6956385a05

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- Fubini integration of a measurable observable of independent streams. -/
theorem solution
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → B)
    (hX : Measurable X) (hY : Measurable Y) (hIndep : IndepFun X Y P)
    (F : A × B → ℂ)
    (hF : Integrable F ((Measure.map X P).prod (Measure.map Y P))) :
    (∫ ω, F (X ω, Y ω) ∂P) =
      ∫ a, ∫ b, F (a, b) ∂(Measure.map Y P) ∂(Measure.map X P) := by
  have hPair : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have hJoint := hIndep.map_prod_eq_prod_map_map
    hX.aemeasurable hY.aemeasurable
  have hFm : AEStronglyMeasurable F
      (Measure.map (fun ω => (X ω, Y ω)) P) := by
    rw [hJoint]
    exact hF.aestronglyMeasurable
  calc
    (∫ ω, F (X ω, Y ω) ∂P) =
        ∫ ab, F ab ∂(Measure.map (fun ω => (X ω, Y ω)) P) :=
      (integral_map hPair.aemeasurable hFm).symm
    _ = ∫ ab, F ab ∂((Measure.map X P).prod (Measure.map Y P)) := by
      rw [hJoint]
    _ = ∫ a, ∫ b, F (a, b) ∂(Measure.map Y P) ∂(Measure.map X P) :=
      integral_prod F hF
