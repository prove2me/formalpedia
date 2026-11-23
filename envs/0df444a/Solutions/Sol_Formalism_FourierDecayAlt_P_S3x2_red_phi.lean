-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.red_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:37.860796+00:00
-- url     : https://prove2.me/submissions/f2295506-70bd-49d0-bf1d-ce6ff1a7baf6

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_hEmb_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_red
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
variable (o : Type) [CommRing o] [IsLocalRing o]
local notation "𝔽" => IsLocalRing.ResidueField o
variable {o} {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (h : GL (Fin k) o) :
    red o (Idx r k) (phi o r k h) = phi 𝔽 r k (red o (Fin k) h) := by
  apply Units.ext
  rw [coe_red, coe_phi, coe_phi, coe_red, hEmb_map]
end Formalism.FourierDecayAlt.P.S3x2
