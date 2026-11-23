-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.int_rdiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:57.752814+00:00
-- url     : https://prove2.me/submissions/b1e9d45c-1f2e-4d9c-afb5-632a5af05c39

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {m : Type} {Y : Matrix m (Fin r) k0} {X : Matrix (Fin r) (Fin r) o} (hX : IsUnit X.det)
    (h : Integral o (Y * X.map (algebraMap o k0))) : Integral o Y := by
  have e : Y = Y * X.map (algebraMap o k0) * X⁻¹.map (algebraMap o k0) := by
    rw [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv X hX]; simp
  rw [e]; exact int_mul h (int_map _)
end Formalism.FourierDecayAlt.P.S3x8
