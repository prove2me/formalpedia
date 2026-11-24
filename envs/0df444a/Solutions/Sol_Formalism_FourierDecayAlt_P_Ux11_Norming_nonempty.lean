-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.Norming.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:26:54.712472+00:00
-- url     : https://prove2.me/submissions/1cc5e101-6c46-490c-a435-c19e21f4bbae

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
    (hN : Norming lam) : Nonempty I := by
  by_contra h
  have := hN 0 (-1) (fun i => (h ⟨i⟩).elim)
  rw [norm_zero] at this
  linarith
end Norming
end Formalism.FourierDecayAlt.P.Ux11
