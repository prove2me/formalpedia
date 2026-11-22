-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.comm_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:26.949074+00:00
-- url     : https://prove2.me/submissions/9f96e5db-bc79-4183-8871-de002419db88

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
theorem _root_.solution {n : ℕ} (f : Fin n → A) (x : A) (hx : ∀ i, x * f i = f i * x) :
    x * (List.ofFn f).prod = (List.ofFn f).prod * x :=
  (Commute.list_prod_right _ _ (by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact hx i)).eq
end Formalism.FourierDecayAlt.P.RuleGD
