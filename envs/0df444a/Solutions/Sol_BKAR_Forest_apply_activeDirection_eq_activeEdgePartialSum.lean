-- Prove2me | solution 1 for BKAR.Forest.apply_activeDirection_eq_activeEdgePartialSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:21:47.684295+00:00
-- url     : https://prove2.me/submissions/db8e58e2-b627-48a6-9698-6a3896fb0fe5

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_partialDeriv_of_hasFDerivAt


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' (F.interpWithFill u t)) :
    ρ' F.activeDirection = F.activeEdgePartialSum u ρ t := by
  rw [activeEdgePartialSum]
  calc
    ρ' F.activeDirection =
        Finset.sum F.activeEdges (fun e => ρ' (edgeBasis e)) := by
          rw [activeDirection, map_sum]
    _ = Finset.sum F.activeEdges
        (fun e => partialDeriv e ρ (F.interpWithFill u t)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [partialDeriv_of_hasFDerivAt e hρ]
end BKAR.Forest
