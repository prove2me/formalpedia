-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.list_sum_flatMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:59.837933+00:00
-- url     : https://prove2.me/submissions/8788b61f-9e8e-4f50-be85-578ccbe5caa6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChainPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
theorem _root_.solution {ι κ : Type} (l : List ι) (f : ι → List κ) (g : κ → E') :
    ((l.flatMap f).map g).sum = (l.map fun i => ((f i).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
