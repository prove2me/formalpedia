-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieBracketMultiplication.op_hasDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:12.93126+00:00
-- url     : https://prove2.me/submissions/8848a181-ebaf-47df-bb92-3dac98d41d6d

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LieBracketMultiplication
variable {k r : ℕ}
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
namespace Formalism.FourierDecayAlt.P.LieBracketMultiplication
theorem _root_.solution (A B : W →L[ℂ] W) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) * B * NormedSpace.exp (s • (-A))) (A * B - B * A) 0 := by
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have ha := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  have hb := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ)
  have h := (ha.mul_const B).mul hb
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg] at h
  rw [← sub_eq_add_neg] at h
  exact h
end Formalism.FourierDecayAlt.P.LieBracketMultiplication
