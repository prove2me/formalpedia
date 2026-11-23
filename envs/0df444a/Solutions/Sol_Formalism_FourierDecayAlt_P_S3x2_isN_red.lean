-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.isN_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:53.825575+00:00
-- url     : https://prove2.me/submissions/62ef6629-ca8e-48f2-891b-606b52710a20

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable (o : Type) [CommRing o] [IsLocalRing o]
local notation "𝔽" => IsLocalRing.ResidueField o
variable {o} {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution {n : GL (Idx r k) o} (hn : IsN (n : Matrix (Idx r k) (Idx r k) o)) :
    IsN (red o (Idx r k) n : Matrix (Idx r k) (Idx r k) 𝔽) :=
  (isN_iff _).2 (((isN_iff _).1 hn).map _)
end Formalism.FourierDecayAlt.P.S3x2
