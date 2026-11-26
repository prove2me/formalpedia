-- Prove2me | solution 1 for BKAR.Forest.measurable_paramValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:36.447833+00:00
-- url     : https://prove2.me/submissions/025b6211-353a-495b-b30f-0630f7f2549f

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Definitions.Def_BKAR_CubePartition_MeasurePartition

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (e : Edge V) :
    Measurable fun u : F.EdgeParam → ℝ => F.paramValue u e := by
  by_cases he : e ∈ F.edges
  · have hfun :
        (fun u : F.EdgeParam → ℝ => F.paramValue u e) =
          fun u : F.EdgeParam → ℝ => u (⟨e, he⟩ : F.EdgeParam) := by
      funext u
      rw [paramValue, dif_pos he]
    rw [hfun]
    exact measurable_pi_apply (⟨e, he⟩ : F.EdgeParam)
  · have hfun :
        (fun u : F.EdgeParam → ℝ => F.paramValue u e) =
          fun _ : F.EdgeParam → ℝ => (1 : ℝ) := by
      funext u
      rw [paramValue, dif_neg he]
    rw [hfun]
    exact measurable_const
end BKAR.Forest
