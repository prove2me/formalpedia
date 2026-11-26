-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i0_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:31.701955+00:00
-- url     : https://prove2.me/submissions/f6c642dc-79c5-446e-a26a-652405af6f8a

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_middle
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_lower
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_i0_upper
import Theorems.Thm_FourierJacobi_Analysis_i0Region_partition
import Theorems.Thm_FourierJacobi_Analysis_i0_four_rows_absolutelySummable


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hP : ‖d * T * V * t‖ < 1)
    (hN : ‖T * V * t / d‖ < 1) (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1)
    (hF : ‖T * U * t ^ 2‖ < 1) (hG : ‖T * U * t ^ 4‖ < 1) :
    Summable (fun p : ℤ × ℤ × ℤ => ‖i0Shell t d U V T p‖) := by
  apply (summable_partition (fun _ => norm_nonneg _) i0Region_partition).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro i
  have h4 := i0_four_rows_absolutelySummable t d U V T ht hP hN hG
  fin_cases i
  · exact h4.1
  · exact h4.2.1
  · exact summable_norm_i0_upper false t d U V T ht hP hE
  · exact summable_norm_i0_middle false t d U V T hP hE hF
  · exact summable_norm_i0_lower false t d U V T hP hF hG
  · exact h4.2.2.1
  · exact h4.2.2.2
  · exact summable_norm_i0_upper true t d U V T ht hN hE
  · exact summable_norm_i0_middle true t d U V T hN hE hF
  · exact summable_norm_i0_lower true t d U V T hN hF hG
end FourierJacobi.Analysis
