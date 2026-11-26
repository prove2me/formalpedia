-- Prove2me | solution 1 for Capacitability.analyticSet_measure_eq_iSup_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:53.730056+00:00
-- url     : https://prove2.me/submissions/ce1111bb-18c4-4b1e-a7da-7f5f46ad8d4b

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_SolutionCapacitability
import Theorems.Thm_MeasureTheory_AnalyticSet_measure_eq_iSup_isCompact


set_option autoImplicit false
open MeasureTheory
open Capacitability
namespace Capacitability
theorem _root_.solution
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    μ A = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), μ K :=
  _root_.MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact hA μ
end Capacitability
