-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.isNU_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:16.818213+00:00
-- url     : https://prove2.me/submissions/a46c1f04-47ad-42d4-a83d-8321d4c162c3

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isNU_set
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
theorem _root_.solution (g : GL (Idx r k) A) :
    IsNU (g : Matrix (Idx r k) (Idx r k) A) ↔ g ∈ PG r (upUniG A k) := by
  rw [isNU_set]
  constructor
  · rintro ⟨g', hg', e⟩; rwa [← Units.ext e]
  · intro hg; exact ⟨g, hg, rfl⟩
end Formalism.FourierDecayAlt.P.S3x2
