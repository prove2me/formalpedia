-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_independent_pair_measurable_image_law_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:13:10.735194+00:00
-- url     : https://prove2.me/submissions/64a5d041-854e-44c0-a972-6f3dafacf3d5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

theorem solution
    {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → B) (Z : A × B → C)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X Y P) :
    Measure.map (fun ω => Z (X ω, Y ω)) P =
      Measure.map Z ((Measure.map X P).prod (Measure.map Y P)) := by
  have hPair : Measurable (fun ω : Ω => (X ω, Y ω)) :=
    hX.prodMk hY
  have hJoint :=
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  calc
    Measure.map (fun ω => Z (X ω, Y ω)) P =
        Measure.map Z (Measure.map (fun ω => (X ω, Y ω)) P) := by
      rw [Measure.map_map hZ hPair]
      rfl
    _ = Measure.map Z ((Measure.map X P).prod (Measure.map Y P)) := by
      rw [hJoint]
