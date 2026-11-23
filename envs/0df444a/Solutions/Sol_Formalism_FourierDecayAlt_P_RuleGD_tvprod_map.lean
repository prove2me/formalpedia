-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.tvprod_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:04.72902+00:00
-- url     : https://prove2.me/submissions/b40531bb-1831-465f-b074-40b14fdc91df

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
theorem _root_.solution (L : LevelData A r) (φ : A →+* A) (Y Y' : ℂ)
    (h : ∀ l, (L.Tvl Y l).map φ = L.Tvl Y' l) : (L.Tvprod Y).map φ = L.Tvprod Y' := by
  unfold LevelData.Tvprod
  rw [← RingHom.mapMatrix_apply, map_list_prod, List.map_reverse, List.map_ofFn]
  exact congrArg (fun f => ((List.ofFn f).reverse).prod) (funext h)
end Formalism.FourierDecayAlt.P.RuleGD
