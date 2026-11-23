-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.isS_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:53.838792+00:00
-- url     : https://prove2.me/submissions/3f79a56b-7722-434e-95e6-a5075baf7ff6

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_mem_PG
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
    IsS x ↔ ∃ g ∈ PG r (⊤ : Subgroup (GL (Fin k) A)), (g : Matrix (Idx r k) (Idx r k) A) = x := by
  constructor
  · rintro ⟨n, _, hn, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨toGL n (isN_isUnit_det hn) * phi A r k (toGL h hh),
      (mem_PG _ _).2 ⟨_, _, Subgroup.mem_top _, hn, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, h, -, hn, rfl⟩ := (mem_PG _ _).1 hg
    exact ⟨n, _, hn, ⟨h, (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit, rfl⟩, rfl⟩
end Formalism.FourierDecayAlt.P.S3x2
