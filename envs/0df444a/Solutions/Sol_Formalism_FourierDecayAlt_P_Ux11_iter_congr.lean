-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.iter_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:27:12.171143+00:00
-- url     : https://prove2.me/submissions/f2426cd4-49bc-48bb-85ec-0b9165e6f4ad

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
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : X → F} {Ω : Set X}
    (hΩ : IsOpen Ω) (h : ∀ y ∈ Ω, f y = g y) {x : X} (hx : x ∈ Ω) (q : ℕ) :
    iteratedFDeriv ℝ q f x = iteratedFDeriv ℝ q g x := by
  rw [← iteratedFDerivWithin_of_isOpen q hΩ hx, ← iteratedFDerivWithin_of_isOpen q hΩ hx]
  exact iteratedFDerivWithin_congr (fun y hy => h y hy) hx q
end Formalism.FourierDecayAlt.P.Ux11
