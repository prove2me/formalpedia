-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.prod_Lp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:35.827212+00:00
-- url     : https://prove2.me/submissions/148aef7e-3dc7-4f59-b7ef-d1268c8d552a

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
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
theorem _root_.solution {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) (g : ℂ → ℂ) :
    ((Lp sl y).map fun l => g l.pt).prod = ∏ a, g (y a) := by
  unfold Lp
  rw [List.map_ofFn, List.prod_ofFn]
  rfl
end Formalism.FourierDecayAlt.P.RealWeightedForms
