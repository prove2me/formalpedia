-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.inPat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:04.091804+00:00
-- url     : https://prove2.me/submissions/f6db722f-6151-4be7-9f54-7bb3c3f9cd03

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k l : ℕ} {Z W : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (hZ : InPat lv k Z) (hW : InPat lv l W) : InPat lv (k + l) (Z * W) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases h1 : lv m < lv i + k
  · rw [hZ i m h1, zero_mul]
  · rw [hW m j (by omega), mul_zero]
end Formalism.L2.SG.Pf.Unip
