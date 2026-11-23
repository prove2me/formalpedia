-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.Dp_Q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:19.295865+00:00
-- url     : https://prove2.me/submissions/0a286933-48bd-4360-96c5-45e63a073a5a

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution (D : Data E W) (T : Tower E) (Th : ℕ → ℕ → E → Pt E → Pt E → ℂ) (ε : ℝ) (k : ℕ)
    (w : W) : (Dp D T Th).Q T ε k w = D.Q T ε k w := by
  unfold TB.Data.Q TB.Data.Sf
  have e : (∑ p ∈ T.X k, ∑ q ∈ T.X k, (Dp D T Th).Kr k p q * (Dp D T Th).gram ε k w p q) =
      ∑ p ∈ T.X k, ∑ q ∈ T.X k, D.Kr k p q * D.gram ε k w p q := by
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    show KrR D T k p q * _ = _
    unfold KrR
    rw [if_pos ⟨hp, hq⟩]
    try rfl
  rw [e]
  try rfl
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
