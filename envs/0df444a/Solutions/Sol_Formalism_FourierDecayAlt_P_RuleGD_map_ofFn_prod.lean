-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.map_ofFn_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:46.897107+00:00
-- url     : https://prove2.me/submissions/d8755c2d-95ce-46b9-8e03-333fc063f92c

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.RuleGD
theorem _root_.solution {n : ℕ} (φ : A →+* A) (f : Fin n → A) (hf : ∀ i, φ (f i) = f i) :
    φ (List.ofFn f).prod = (List.ofFn f).prod := by
  rw [map_list_prod, List.map_ofFn]
  have : (⇑φ ∘ f) = f := funext hf
  rw [this]
end Formalism.FourierDecayAlt.P.RuleGD
