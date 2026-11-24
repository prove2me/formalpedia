-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.expW_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:03.286125+00:00
-- url     : https://prove2.me/submissions/fa91c571-1dcb-468e-a9a9-e4f200c8947d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution (w : List (Bool × Mat k r)) : (expW w).map Prod.snd = bw (w.map Prod.fst) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [expW, List.map_cons, bw, ← ih, List.map_flatMap, List.flatMap_map, List.map_map,
      Function.comp_def]
end Formalism.FourierDecayAlt.P.ListSumInequalities
