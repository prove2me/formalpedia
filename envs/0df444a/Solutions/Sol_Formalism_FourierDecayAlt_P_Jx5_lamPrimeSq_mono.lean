-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx5.lamPrimeSq_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:42.567942+00:00
-- url     : https://prove2.me/submissions/4635193f-b7c9-4022-99e1-f1b0b997cba1

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx5
namespace Formalism.FourierDecayAlt.P.Jx5
theorem _root_.solution (m i : ℕ) {C C' κ N I A TT : ℝ} (hC : 0 ≤ C) (h : C ≤ C') (hκ : 0 ≤ κ)
    (hN : 0 ≤ N) (hI : 0 ≤ I) (hA : 0 ≤ A) :
    Sz.lamPrimeSq m i C κ N I A TT ≤ Sz.lamPrimeSq m i C' κ N I A TT := by
  have hC' : 0 ≤ C' := hC.trans h
  unfold Sz.lamPrimeSq
  gcongr
end Formalism.FourierDecayAlt.P.Jx5
