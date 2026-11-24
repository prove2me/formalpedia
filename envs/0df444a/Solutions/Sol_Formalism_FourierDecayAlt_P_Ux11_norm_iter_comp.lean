-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.norm_iter_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:27:13.689806+00:00
-- url     : https://prove2.me/submissions/da785936-fec5-4755-9452-7ea24e0d7d2b

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
theorem _root_.solution {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : F →L[ℝ] G) {g : X → F} {Ω : Set X} {n : WithTop ℕ∞} (hg : ContDiffOn ℝ n g Ω)
    (hΩ : IsOpen Ω) {x : X} (hx : x ∈ Ω) {q : ℕ} (hq : (q : WithTop ℕ∞) ≤ n) :
    ‖iteratedFDeriv ℝ q (fun y => L (g y)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ q g x‖ := by
  rw [← iteratedFDerivWithin_of_isOpen q hΩ hx, ← iteratedFDerivWithin_of_isOpen q hΩ hx]
  exact L.norm_iteratedFDerivWithin_comp_left (hg x hx) hΩ.uniqueDiffOn hx hq
end Formalism.FourierDecayAlt.P.Ux11
