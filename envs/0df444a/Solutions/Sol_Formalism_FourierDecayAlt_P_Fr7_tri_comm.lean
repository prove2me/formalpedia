-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.tri_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:46.773922+00:00
-- url     : https://prove2.me/submissions/764d2848-e921-4936-838e-91009780abef

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
namespace Formalism.FourierDecayAlt.P.Fr7
theorem _root_.solution {B : Type} [Ring B] [Algebra ℂ B] (b b' t t' e n : B) (D D' : ℂ)
    (hee : e * e = e) (hen : e * n = n) (hne : n * e = 0) (hnn : n * n = 0)
    (eb : e * b = b * e) (eb' : e * b' = b' * e) (et : e * t = t * e) (et' : e * t' = t' * e)
    (nb : n * b = b * n) (nb' : n * b' = b' * n) (nt : n * t = t * n) (nt' : n * t' = t' * n)
    (hbb : b * b' = b' * b)
    (K : (D - 1) • (b * t') + D' • (t * b') = (D' - 1) • (b' * t) + D • (t' * b)) :
    Commute (D • b - b * e - t * n) (D' • b' - b' * e - t' * n) := by
  have eb_x : ∀ x, e * (b * x) = b * (e * x) := fun x => by rw [← mul_assoc, eb, mul_assoc]
  have eb'_x : ∀ x, e * (b' * x) = b' * (e * x) := fun x => by rw [← mul_assoc, eb', mul_assoc]
  have et_x : ∀ x, e * (t * x) = t * (e * x) := fun x => by rw [← mul_assoc, et, mul_assoc]
  have et'_x : ∀ x, e * (t' * x) = t' * (e * x) := fun x => by rw [← mul_assoc, et', mul_assoc]
  have nb_x : ∀ x, n * (b * x) = b * (n * x) := fun x => by rw [← mul_assoc, nb, mul_assoc]
  have nb'_x : ∀ x, n * (b' * x) = b' * (n * x) := fun x => by rw [← mul_assoc, nb', mul_assoc]
  have nt_x : ∀ x, n * (t * x) = t * (n * x) := fun x => by rw [← mul_assoc, nt, mul_assoc]
  have nt'_x : ∀ x, n * (t' * x) = t' * (n * x) := fun x => by rw [← mul_assoc, nt', mul_assoc]
  have bb_x : ∀ x, b * (b' * x) = b' * (b * x) := fun x => by rw [← mul_assoc, hbb, mul_assoc]
  have Kn := congrArg (· * n) K
  simp only [add_mul, smul_mul_assoc, mul_assoc] at Kn
  show _ * _ = _ * _
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, smul_sub, eb_x, eb'_x,
    et_x, et'_x, nb_x, nb'_x, nt_x, nt'_x, bb_x, eb, eb', nb, nb', hee, hen, hne, hnn, hbb, mul_zero,
    sub_zero]
  linear_combination (norm := module) (-1 : ℂ) • Kn
end Formalism.FourierDecayAlt.P.Fr7
