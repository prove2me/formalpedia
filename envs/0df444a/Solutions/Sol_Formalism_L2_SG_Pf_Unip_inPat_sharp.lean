-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.inPat_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:05.814842+00:00
-- url     : https://prove2.me/submissions/9a64832e-0b2a-4f31-a685-2337183c2efa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
variable {lv : ι → ℕ} {T k : ℕ}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution {J J' Z : Matrix ι ι K} (hJ : Graded lv T J) (hJ' : Graded lv T J') (hZ : InPat lv k Z) :
    InPat lv k (sharp J J' Z) := by
  intro i j hij
  unfold sharp
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.conjTranspose_apply]
  by_cases ha : J' i a = 0
  · simp [ha]
  by_cases hb : J b j = 0
  · simp [hb]
  have e1 := hJ' i a ha
  have e2 := hJ b j hb
  rw [hZ b a (by omega), star_zero, mul_zero, zero_mul]
end Formalism.L2.SG.Pf.Unip
