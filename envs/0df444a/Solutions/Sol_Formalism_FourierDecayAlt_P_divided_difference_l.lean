-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.divided_difference_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:54.454853+00:00
-- url     : https://prove2.me/submissions/2e660860-4d1f-45ce-8a3e-c8c8d7cb38d6

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : EtaLevel := by
  intro A S _ _ _ _ _ _ r L f Y Ya hY
  have hc : Y - Ya ≠ 0 := sub_ne_zero.mpr hY
  have hio : ∀ (c : ℂ) (x : A),
      (Matrix.scalar (Ix S) (c • x) : SlopeTestRemainingChoices S A) = c • Matrix.scalar (Ix S) x := by
    intro c x
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, smul_ite] <;> split_ifs <;> simp
  have hl0 : L.l0 Y - L.l0 Ya = -((Y - Ya) • (L.ζb * L.GGi)) := by
    simp only [Formalism.FourierDecayAlt.R.LevelData.l0, ← Algebra.smul_def, sub_smul, add_smul]
    abel
  simp only [Formalism.FourierDecayAlt.Fr.FrameData.l, Formalism.FourierDecayAlt.Fr.FrameData.DD, Formalism.FourierDecayAlt.Fr.kapL, io]
  have e : Matrix.scalar (Ix S) (L.l0 Y) + Matrix.scalar (Ix S) (L.ζb * L.ζi * L.GGi) * f.ee Y -
      (Matrix.scalar (Ix S) (L.l0 Ya) + Matrix.scalar (Ix S) (L.ζb * L.ζi * L.GGi) * f.ee Ya) =
      Matrix.scalar (Ix S) (L.l0 Y - L.l0 Ya) +
        Matrix.scalar (Ix S) (L.ζb * L.ζi * L.GGi) * (f.ee Y - f.ee Ya) := by
    rw [map_sub, mul_sub]
    abel
  rw [e, hl0, map_neg, hio, smul_add, mul_smul_comm, smul_neg, smul_smul, inv_mul_cancel₀ hc, one_smul]
end Formalism.FourierDecayAlt.P
