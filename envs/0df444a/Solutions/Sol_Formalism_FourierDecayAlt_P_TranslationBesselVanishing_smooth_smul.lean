-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:38:04.447196+00:00
-- url     : https://prove2.me/submissions/65fa6e96-2ac6-4f5a-a42d-8cca6a9cd2a4

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
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (c : ℂ) {x : H}
    (hx : x ∈ smoothVecs (k := k) (r := r) σ) : c • x ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g (c • x))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g x) from hx) g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgl => ?_⟩
  simp only [map_smul, hFe g hg hgl]
end Formalism.FourierDecayAlt.P.TranslationBesselVanishing
