-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.int_ldiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:22.566251+00:00
-- url     : https://prove2.me/submissions/5c79766f-5e33-48dc-a275-4d9194743b56

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
theorem _root_.solution {m : Type} {Y : Matrix (Fin r) m k0} {X : Matrix (Fin r) (Fin r) o} (hX : IsUnit X.det)
    (h : Integral o (X.map (algebraMap o k0) * Y)) : Integral o Y := by
  have e : Y = X⁻¹.map (algebraMap o k0) * (X.map (algebraMap o k0) * Y) := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul X hX]; simp
  rw [e]; exact int_mul (int_map _) h
end Formalism.FourierDecayAlt.P.S3x8
