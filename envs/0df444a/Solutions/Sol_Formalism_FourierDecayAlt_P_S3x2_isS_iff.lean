-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.isS_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:44.2315+00:00
-- url     : https://prove2.me/submissions/5e676ac0-5833-460b-8ee3-33515f2e0bf2

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isS_set
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
    IsS (g : Matrix (Idx r k) (Idx r k) A) ↔ g ∈ PG r (⊤ : Subgroup (GL (Fin k) A)) := by
  rw [isS_set]
  constructor
  · rintro ⟨g', hg', e⟩; rwa [← Units.ext e]
  · intro hg; exact ⟨g, hg, rfl⟩
end Formalism.FourierDecayAlt.P.S3x2
