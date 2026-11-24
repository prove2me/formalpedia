-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:01.594957+00:00
-- url     : https://prove2.me/submissions/3c32ce0a-bb41-4e3f-ad1f-ef439651feca

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
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {x y : H}
    (hx : x ∈ smoothVecs (k := k) (r := r) σ) (hy : y ∈ smoothVecs (k := k) (r := r) σ) :
    x + y ∈ smoothVecs (k := k) (r := r) σ := by
  show SmoothOnH (Hpk k r) (fun g => σ g (x + y))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g x) from hx) g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hGe⟩ := (show SmoothOnH (Hpk k r) (fun g => σ g y) from hy) g₀ hg₀
  refine ⟨U ∩ V, fun g => F g + G g, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
  simp only [map_add, hFe g hg.1 hgl, hGe g hg.2 hgl]
end Formalism.FourierDecayAlt.P.TranslationBesselVanishing
