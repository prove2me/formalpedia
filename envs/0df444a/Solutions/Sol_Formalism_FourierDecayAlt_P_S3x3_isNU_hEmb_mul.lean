-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.isNU_hEmb_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:20.976031+00:00
-- url     : https://prove2.me/submissions/2e5fc498-1750-4988-aefc-3c91b72523bb

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_hEmb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_hEmb_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_isN_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x3
theorem _root_.solution {u : Matrix (Fin k) (Fin k) A} (hu : IsUpUni u)
    {n : Matrix (Idx r k) (Idx r k) A} (hn : IsN n) : IsNU (hEmb r u * n) := by
  have hdet : IsUnit u.det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det A hu]; exact isUnit_one
  refine ⟨hEmb r u * n * hEmb r u⁻¹, hEmb r u, isN_conj (Matrix.mul_nonsing_inv u hdet) hn,
    ⟨u, hu, rfl⟩, ?_⟩
  rw [mul_assoc, ← hEmb_mul, Matrix.nonsing_inv_mul u hdet, hEmb_one, mul_one]
end Formalism.FourierDecayAlt.P.S3x3
