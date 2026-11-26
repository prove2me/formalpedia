-- Prove2me | solution 1 for BKAR.BKARContDiff.mixedPartialList_eq_of_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:56.681587+00:00
-- url     : https://prove2.me/submissions/83d19666-8a3b-418a-8fd8-45a5273f5420

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_PartialDerivSymmetry
import Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_cons_cons_comm

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    {es₁ es₂ : List (Edge V)} (hperm : es₁.Perm es₂)
    (hρ : BKARContDiff ρ) :
    BKAR.mixedPartialList es₁ ρ =
      BKAR.mixedPartialList es₂ ρ := by
  induction hperm generalizing ρ with
  | nil =>
      rfl
  | cons e hperm ih =>
      change BKAR.partialDeriv e
          (BKAR.mixedPartialList _ ρ) =
        BKAR.partialDeriv e
          (BKAR.mixedPartialList _ ρ)
      rw [ih hρ]
  | swap e f es =>
      exact (hρ.mixedPartialList_cons_cons_comm e f es).symm
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ hρ).trans (ih₂ hρ)
end BKAR.BKARContDiff
