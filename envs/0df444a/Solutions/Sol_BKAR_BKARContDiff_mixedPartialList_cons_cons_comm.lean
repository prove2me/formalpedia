-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_cons_cons_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:46.897821+00:00
-- url     : https://prove2.me/submissions/95381e03-0ccb-47bf-b524-61fef2305d2c

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_PartialDerivSymmetry
import Theorems.Thm_BKAR_BKARContDiff_partialDeriv_comm

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (e f : Edge V) (es : List (Edge V)) :
    BKAR.mixedPartialList (e :: f :: es) ρ =
      BKAR.mixedPartialList (f :: e :: es) ρ := by
  exact (hρ.mixedPartialList es).partialDeriv_comm e f
end BKAR.BKARContDiff
