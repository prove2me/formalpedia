-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.restrict_form_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:43.873805+00:00
-- url     : https://prove2.me/submissions/72aa2dc7-9a87-4205-8a5b-01b96d1a22da

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h) (W : Submodule K V) :
    Herm (restrictFormAlt h W) := fun u v => hh u v
end Formalism.FourierDecayAlt.P.S3x6
