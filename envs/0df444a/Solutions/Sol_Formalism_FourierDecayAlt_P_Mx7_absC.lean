-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.absC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:50.342586+00:00
-- url     : https://prove2.me/submissions/029d326f-3b22-4a5d-87c9-0e31cbd3901f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
variable {R : Type*} [Ring R] [Algebra ℂ R]
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (G Gi z zb N Ns K : R) (t : ℂ) (hGGi : G * Gi = 1) (hGdef : G = z * zb - algebraMap ℂ R t)
    (czzb : z * zb = zb * z) (cGiz : Gi * z = z * Gi) (cGizb : Gi * zb = zb * Gi)
    (nz : N * z = z * N + 1) (nGi : N * Gi = Gi * N - zb * Gi * Gi)
    (nszb : Ns * zb = zb * Ns - 1) (nsGi : Ns * Gi = Gi * Ns + z * Gi * Gi)
    (hcurv : Ns * N - N * Ns = K * Gi * Gi) (cu cv : ℂ) :
    (-Ns - cu • (z * Gi)) * (-N - cv • (zb * Gi)) - (-N - cv • (zb * Gi)) * (-Ns - cu • (z * Gi)) =
      K * Gi * Gi + ((cu + cv) * t) • (Gi * Gi) := by
  have hzz : z * zb = G + t • 1 := by rw [hGdef, Algebra.algebraMap_eq_smul_one]; abel
  have w1 : z * zb * Gi * Gi = Gi + t • (Gi * Gi) := by
    rw [hzz, add_mul, add_mul, hGGi, one_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
  have k1 : Ns * (zb * Gi) = (zb * Gi) * Ns + t • (Gi * Gi) := by
    calc Ns * (zb * Gi) = (Ns * zb) * Gi := (mul_assoc _ _ _).symm
      _ = zb * (Ns * Gi) - Gi := by rw [nszb, sub_mul, one_mul, mul_assoc]
      _ = zb * Gi * Ns + (zb * z) * Gi * Gi - Gi := by rw [nsGi, mul_add]; simp only [mul_assoc]
      _ = _ := by rw [← czzb, w1]; abel
  have k2 : N * (z * Gi) = (z * Gi) * N - t • (Gi * Gi) := by
    calc N * (z * Gi) = (N * z) * Gi := (mul_assoc _ _ _).symm
      _ = z * (N * Gi) + Gi := by rw [nz, add_mul, one_mul, mul_assoc]
      _ = z * Gi * N - (z * zb) * Gi * Gi + Gi := by rw [nGi, mul_sub]; simp only [mul_assoc]
      _ = _ := by rw [w1]; abel
  have k3 : (z * Gi) * (zb * Gi) = (zb * Gi) * (z * Gi) := by
    calc (z * Gi) * (zb * Gi) = z * (Gi * zb) * Gi := by simp only [mul_assoc]
      _ = (z * zb) * Gi * Gi := by rw [cGizb]; simp only [mul_assoc]
      _ = zb * (z * Gi) * Gi := by rw [czzb]; simp only [mul_assoc]
      _ = zb * (Gi * z) * Gi := by rw [cGiz]
      _ = _ := by simp only [mul_assoc]
  have ex : (-Ns - cu • (z * Gi)) * (-N - cv • (zb * Gi)) - (-N - cv • (zb * Gi)) * (-Ns - cu • (z * Gi)) =
      (Ns * N - N * Ns) + cv • (Ns * (zb * Gi) - (zb * Gi) * Ns) - cu • (N * (z * Gi) - (z * Gi) * N) +
        (cu * cv) • ((z * Gi) * (zb * Gi) - (zb * Gi) * (z * Gi)) := by
    simp only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    module
  rw [ex, hcurv, k1, k2, k3]
  module
end Formalism.FourierDecayAlt.P.Mx7
