-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.Norming.eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:27:20.500892+00:00
-- url     : https://prove2.me/submissions/91d3547a-4345-4e8d-bd90-c27869d16aa4

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.Ux11
namespace Norming
theorem _root_.solution {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {lam : I → V →L[ℝ] E}
    (hN : Norming lam) {v w : V} (h : ∀ i, lam i v = lam i w) : v = w := by
  have := hN (v - w) 0 (fun i => by rw [map_sub, h i, sub_self, norm_zero])
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
end Norming
end Formalism.FourierDecayAlt.P.Ux11
