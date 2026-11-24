-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:55:17.725123+00:00
-- url     : https://prove2.me/submissions/9b749598-d001-4e9c-9174-72fd85ac4cda

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_sigma_mul

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
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    σ g v ∈ smoothVecs (k := k) (r := r) σ := by
  intro h0 hh0
  obtain ⟨U, F, hU, hmem, hF, hEq⟩ := hv (h0 * g) (uh_mul hh0 hg)
  refine ⟨(mulRightCLM g) ⁻¹' U, fun h => F (h * g), hU.preimage (mulRightCLM g).continuous, hmem,
    hF.comp (mulRightCLM g).contDiff.contDiffOn (fun h hh => hh), ?_⟩
  intro h hhU hh
  have e := (hEq (h * g) hhU (uh_mul hh hg)).symm
  show σ h (σ g v) = F (h * g)
  rw [e]
  show σ h (σ g v) = σ (h * g) v
  rw [sigma_mul hds hh hg]
  rfl
end Formalism.FourierDecayAlt.P.TranslationBesselVanishing
