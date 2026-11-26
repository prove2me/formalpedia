-- Prove2me | solution 1 for BKAR.BKARContDiff.partialDeriv_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:50.175725+00:00
-- url     : https://prove2.me/submissions/8904f234-f79a-4d80-b4d7-6046fbe8880a

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_PartialDerivSymmetry
import Theorems.Thm_BKAR_BKARContDiff_partialDeriv_comm_apply

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (e f : Edge V) :
    BKAR.partialDeriv e (BKAR.partialDeriv f ρ) =
      BKAR.partialDeriv f (BKAR.partialDeriv e ρ) := by
  funext x
  exact hρ.partialDeriv_comm_apply e f x
end BKAR.BKARContDiff
