-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.isN_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:11.633371+00:00
-- url     : https://prove2.me/submissions/1351308a-157e-468e-b66f-eceb3d0a8525

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_isUnit_det

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
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (x : Matrix (Idx r k) (Idx r k) A) :
    IsN x ↔ ∃ g ∈ UcG A (cI r k), (g : Matrix (Idx r k) (Idx r k) A) = x := by
  constructor
  · intro hx
    exact ⟨toGL x (isN_isUnit_det hx), (isN_iff x).1 hx, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact (isN_iff _).2 hg
end Formalism.FourierDecayAlt.P.S3x2
