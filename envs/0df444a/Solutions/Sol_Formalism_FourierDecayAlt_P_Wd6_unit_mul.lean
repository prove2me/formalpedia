-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:01.280068+00:00
-- url     : https://prove2.me/submissions/5c00b2c1-63e3-449b-8d47-e4a6ac231b8d

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_mul_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_io

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (a : S) (i j r s : Fin 2) (x y : A) :
    ((eU a i j : SlopeTestRemainingChoices S A) * io x) * (eU a r s * io y) = if j = r then eU a i s * io (x * y) else 0 := by
  calc ((eU a i j : SlopeTestRemainingChoices S A) * io x) * (eU a r s * io y)
      = eU a i j * (io x * eU a r s) * io y := by simp only [mul_assoc]
    _ = eU a i j * (eU a r s * io x) * io y := by rw [(eU_io a r s x).eq]
    _ = (eU a i j * eU a r s) * (io x * io y) := by simp only [mul_assoc]
    _ = _ := by rw [eU_mul_eU, ← io_mul]; split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Wd6
