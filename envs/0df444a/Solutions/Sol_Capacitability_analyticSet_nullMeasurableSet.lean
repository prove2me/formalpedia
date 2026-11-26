-- Prove2me | solution 1 for Capacitability.analyticSet_nullMeasurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:56.552673+00:00
-- url     : https://prove2.me/submissions/5794c5af-8f64-4231-9620-d04b2ee87f65

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_SolutionCapacitability
import Theorems.Thm_MeasureTheory_AnalyticSet_nullMeasurableSet


set_option autoImplicit false
open MeasureTheory
open Capacitability
namespace Capacitability
theorem _root_.solution
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet A μ :=
  _root_.MeasureTheory.AnalyticSet.nullMeasurableSet hA μ
end Capacitability
