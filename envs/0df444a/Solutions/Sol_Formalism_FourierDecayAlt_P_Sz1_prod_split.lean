-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz1.prod_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:08.118371+00:00
-- url     : https://prove2.me/submissions/199eeba5-4107-4040-84ba-c9d2532ddeeb

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz1
theorem _root_.solution (k d : ℕ) (q : ℝ) :
    ∏ i ∈ range (k + d), (1 - (q ^ (i + 1))⁻¹) =
      (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) * ∏ j ∈ Ioc k (k + d), (1 - (q ^ j)⁻¹) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_Ioc_succ_top (by omega), ih, mul_assoc]
end Formalism.FourierDecayAlt.P.Sz1
