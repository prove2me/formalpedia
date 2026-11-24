-- Prove2me | solution 1 for FockRL.kroneckerMap_one_right_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:08.55365+00:00
-- url     : https://prove2.me/submissions/183fdff2-eec3-4e2e-a20b-2bc0087928ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero

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
open FockRL
namespace FockRL
theorem _root_.solution {p q r s : ℕ} (Z : FockH1Action.Mat p q) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s) (a, b) (a', b') ≠ 0) :
    Z a a' ≠ 0 ∧ b = b' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with hb
  · exact ⟨by simpa using h, hb⟩
  · simp at h
end FockRL
