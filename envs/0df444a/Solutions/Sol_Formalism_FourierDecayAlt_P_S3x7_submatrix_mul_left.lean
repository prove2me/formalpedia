-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.submatrix_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:53.039489+00:00
-- url     : https://prove2.me/submissions/1bcecb11-6da1-4c3b-95ad-2d08f4f30d08

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {l r : ℕ} {m : Type} (e : Fin l → Fin r) (he : Function.Injective e)
    (P M : Matrix (Fin r) (Fin r) A) (f : m → Fin r)
    (h : ∀ a k, k ∉ Set.range e → P (e a) k = 0) :
    (P * M).submatrix e f = P.submatrix e e * M.submatrix e f := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective e he _ _ ?_ ?_).symm
  · intro k hk; rw [h a k hk, zero_mul]
  · intro k; rfl
end Formalism.FourierDecayAlt.P.S3x7
