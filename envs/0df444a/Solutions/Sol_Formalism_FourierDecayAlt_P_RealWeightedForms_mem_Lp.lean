-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.mem_Lp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:22:41.667962+00:00
-- url     : https://prove2.me/submissions/38869bf9-42bf-4439-b791-e2eb616a723c

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
theorem _root_.solution {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) (a : Fin K) :
    (⟨true, sl a, (y a : ℂ)⟩ : Letter ℂ S) ∈ Lp sl y := by
  unfold Lp
  rw [List.mem_ofFn]
  exact ⟨a, rfl⟩
end Formalism.FourierDecayAlt.P.RealWeightedForms
