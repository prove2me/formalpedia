-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.phi_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:11.622798+00:00
-- url     : https://prove2.me/submissions/06b5e02d-d06e-4c6b-b72c-260e149cc5f8

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_hEmb_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x2.coe_phi

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution : Function.Injective (phi A r k) := by
  intro a b hab
  apply Units.ext
  ext i j
  have h1 : hEmb r (a : Matrix (Fin k) (Fin k) A) = hEmb r (b : Matrix (Fin k) (Fin k) A) := by
    rw [← coe_phi, ← coe_phi, hab]
  rw [← hEmb_apply (r := r) (a : Matrix (Fin k) (Fin k) A), h1, hEmb_apply]
end Formalism.FourierDecayAlt.P.S3x2
