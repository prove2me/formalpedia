-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.t21_commutator_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:50.156853+00:00
-- url     : https://prove2.me/submissions/8db2be52-3cfc-4d90-a6cf-24a1427aee67

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {B : Type} [Ring B]
namespace Formalism.FourierDecayAlt.P.Fr10
theorem _root_.solution [Algebra ℂ B] (a c a' c' : B) (Y Y' Yb : ℂ) (hne : Y ≠ Y')
    (h1 : (Y - Y') • (a * c' - c' * a) = c * a' - c' * a)
    (h2 : (Y' - Y) • (a' * c - c * a') = c' * a - c * a') :
    -a * ((Yb - Y') • c') + ((Yb - Y - 1) • c) * (-a') = -a' * ((Yb - Y) • c) + ((Yb - Y' - 1) • c') * (-a) := by
  have hXZ : a * c' - c' * a + (c * a' - a' * c) = 0 := by
    have h : (Y - Y') • (a * c' - c' * a + (c * a' - a' * c)) = 0 := by
      linear_combination (norm := module) h1 + h2
    exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
  simp only [neg_mul, mul_neg, mul_smul_comm, smul_mul_assoc]
  linear_combination (norm := module) (-(Yb - Y)) • hXZ - h1
end Formalism.FourierDecayAlt.P.Fr10
