-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.Rht0_J
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:53.009943+00:00
-- url     : https://prove2.me/submissions/623dea2f-e7f9-4806-bd1e-fa9df62bf444

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_partial_flip_mul_J_insert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution (a : S) (d D : K) (h : D = 1 - d) (hd : d ≠ 0) (hd1 : d ≠ 1) :
    Rht0 a d * d0 (ins a JJ) = (d / (d - 1)) • (d0 (ins a JJ) * Rh0 a D) := by
  have h1 : d - 1 ≠ 0 := sub_ne_zero.mpr hd1
  have hc : d / (d - 1) * (1 - d - 1)⁻¹ = -(d - 1)⁻¹ := by
    rw [show 1 - d - 1 = -d by ring, inv_neg]
    field_simp
  subst h
  unfold Rh0 Rht0
  rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, partial_flip_mul_J_insert, Matrix.mul_smul,
    smul_smul, hc, neg_smul, ← smul_neg]
  congr 1
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, sub_smul, one_smul]
  abel
end Formalism.FourierDecayAlt.P.Wd9
