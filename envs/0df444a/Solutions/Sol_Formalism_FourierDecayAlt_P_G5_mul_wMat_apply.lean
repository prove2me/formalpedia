-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mul_wMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:20.137338+00:00
-- url     : https://prove2.me/submissions/dc64a076-4b9c-4ab4-8ce2-153ca231d435

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (A * wMat n) i j = A i j.rev := by
  have h : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => by
    rw [eq_iff_iff]
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [wMat, Matrix.mul_apply, h]
end Formalism.FourierDecayAlt.P.G5
