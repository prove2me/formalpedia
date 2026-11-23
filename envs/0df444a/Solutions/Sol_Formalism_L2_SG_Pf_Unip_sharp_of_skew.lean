-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.sharp_of_skew
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:22.674195+00:00
-- url     : https://prove2.me/submissions/e0e9f7f3-063b-4c4c-ab42-c24066018577

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
variable {J J' : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution (h : J' * J = 1) {X : Matrix ι ι K} (hX : Xᴴ * J = -(J * X)) : sharp J J' X = -X := by
  unfold sharp
  rw [Matrix.mul_assoc, hX, Matrix.mul_neg, ← Matrix.mul_assoc, h, Matrix.one_mul]
end Formalism.L2.SG.Pf.Unip
