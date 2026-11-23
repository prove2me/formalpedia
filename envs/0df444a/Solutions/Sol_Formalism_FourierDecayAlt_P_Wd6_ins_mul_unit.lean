-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.ins_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:39.927878+00:00
-- url     : https://prove2.me/submissions/6ca8c6ec-186c-432b-9e79-ed6f10bddd02

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_unit_mul

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
theorem _root_.solution (a : S) (k j : Fin 2) (x : A) (N : M2 A) :
    ins a (lift0 N) * (io x * (eU a k j : SlopeTestRemainingChoices S A)) = ∑ r, eU a r j * io (N r k * x) := by
  unfold ins lift0
  rw [← (eU_io a k j x).eq]
  simp only [Finset.sum_mul, Matrix.map_apply, unit_mul]
  simp
end Formalism.FourierDecayAlt.P.Wd6
