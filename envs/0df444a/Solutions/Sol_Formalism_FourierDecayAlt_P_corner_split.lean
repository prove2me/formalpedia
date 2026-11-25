-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.corner_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:26.735848+00:00
-- url     : https://prove2.me/submissions/be650f4a-26df-4ec8-8247-92c926332f96

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.CornerSplit := by
  intro m X B ρ₁ ρ' t
  simp only [Cof, R0, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_mul,
    Nat.add_sub_cancel]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_mul, Finset.sum_mul]; ring
end Formalism.FourierDecayAlt.P
