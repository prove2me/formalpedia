-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.mem_PG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:35.032478+00:00
-- url     : https://prove2.me/submissions/51dcc669-c3fe-474b-8b83-fb28cb52b451

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
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (V : Subgroup (GL (Fin k) A)) (g : GL (Idx r k) A) :
    g ∈ PG r V ↔ ∃ n : GL (Idx r k) A, ∃ h ∈ V, IsN (n : Matrix (Idx r k) (Idx r k) A) ∧
      g = n * phi A r k h := by
  constructor
  · rintro ⟨n, hn, _, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨n, h, hh, (isN_iff _).2 hn, rfl⟩
  · rintro ⟨n, h, hh, hn, rfl⟩
    exact ⟨n, (isN_iff _).1 hn, _, ⟨h, hh, rfl⟩, rfl⟩
end Formalism.FourierDecayAlt.P.S3x2
