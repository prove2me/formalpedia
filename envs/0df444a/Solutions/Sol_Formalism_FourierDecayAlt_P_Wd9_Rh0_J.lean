-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.Rh0_J
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:32.312133+00:00
-- url     : https://prove2.me/submissions/6dca1271-e630-43a2-84bb-389dd97e89ca

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_flip_mul_J_insert

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
theorem _root_.solution (a : S) (D d : K) (h : d = 1 - D) (hD : D ≠ 0) (hD1 : D ≠ 1) :
    Rh0 a D * d0 (ins a JJ) = (D / (D - 1)) • (d0 (ins a JJ) * Rht0 a d) := by
  have h1 : D - 1 ≠ 0 := sub_ne_zero.mpr hD1
  have hc : D / (D - 1) * (1 - D - 1)⁻¹ = -(D - 1)⁻¹ := by
    rw [show 1 - D - 1 = -D by ring, inv_neg]
    field_simp
  subst h
  unfold Rh0 Rht0
  rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, flip_mul_J_insert, Matrix.mul_smul,
    smul_smul, hc, neg_smul, ← smul_neg]
  congr 1
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, sub_smul, one_smul]
  abel
end Formalism.FourierDecayAlt.P.Wd9
