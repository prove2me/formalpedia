-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.coe_red
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:11.411547+00:00
-- url     : https://prove2.me/submissions/23af1a08-9d4c-4b97-9dec-f5a45744f397

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective

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
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι o) :
    (red o ι g : Matrix ι ι 𝔽) = (g : Matrix ι ι o).map (IsLocalRing.residue o) := rfl
end Formalism.FourierDecayAlt.P.S3x2
