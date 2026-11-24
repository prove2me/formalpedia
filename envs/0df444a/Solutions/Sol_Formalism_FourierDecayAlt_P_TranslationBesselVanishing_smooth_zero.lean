-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:54:05.025163+00:00
-- url     : https://prove2.me/submissions/626ef849-86c6-4ae0-89ba-f21c2f0e3708

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open PI.UpqRep
open Formalism.FourierDecayAlt.P.TranslationBesselVanishing
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TranslationBesselVanishing
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} :
    (0 : H) ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g 0)
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => by simp⟩
end Formalism.FourierDecayAlt.P.TranslationBesselVanishing
