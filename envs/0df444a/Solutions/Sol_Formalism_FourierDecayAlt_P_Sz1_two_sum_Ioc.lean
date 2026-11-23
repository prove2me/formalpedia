-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz1.two_sum_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:38.059636+00:00
-- url     : https://prove2.me/submissions/8940f810-a63b-45aa-ab6b-86364b244802

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
theorem _root_.solution (k p : ℕ) : 2 * ∑ M ∈ Ioc k (k + p), M = 2 * (p * k) + p * (p + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), mul_add, ih]; ring
end Formalism.FourierDecayAlt.P.Sz1
