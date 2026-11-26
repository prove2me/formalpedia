-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_i0_upper_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:55.185295+00:00
-- url     : https://prove2.me/submissions/ac16d2fc-f3b8-49da-ac80-c4fe8c483ec2

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0_upper_reindexed
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_three_geometric


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (neg : Bool) (t d U V T : ℂ)
    (ht : ‖t ^ 2‖ < 1) (hK : ‖i0KRatio neg t d V T‖ < 1)
    (hE : ‖(T * V) ^ 2 * t ^ 2‖ < 1) :
    Summable (fun n : Fin 2 × ℕ × ℕ × ℕ =>
      ‖i0Shell t d U V T (i0UpperRowEquiv neg n).val‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro e
  convert summable_norm_three_geometric
    ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * V) ^ (e.val + 1) * t ^ 2)
    (i0KRatio neg t d V T) ((T * V) ^ 2 * t ^ 2) (t ^ 2) hK hE ht using 1
  exact funext fun n => congrArg norm (i0_upper_reindexed neg t d U V T e n)
end FourierJacobi.Analysis
