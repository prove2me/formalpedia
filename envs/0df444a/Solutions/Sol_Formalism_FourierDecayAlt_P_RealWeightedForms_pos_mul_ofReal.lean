-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.pos_mul_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:22:38.423904+00:00
-- url     : https://prove2.me/submissions/ecd40065-ea58-4e35-b5ec-f288c7a9f94a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
variable {S : Type}
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
theorem _root_.solution {z : ℂ} {r : ℝ} (hz : z.im = 0 ∧ 0 < z.re) (hr : 0 < r) :
    (z * r).im = 0 ∧ 0 < (z * r).re := by
  refine ⟨by simp [hz.1], ?_⟩
  have e : (z * r).re = z.re * r := by simp [hz.1]
  rw [e]
  exact mul_pos hz.2 hr
end Formalism.FourierDecayAlt.P.RealWeightedForms
