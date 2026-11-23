-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.geom_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:03.54801+00:00
-- url     : https://prove2.me/submissions/ffc82dfc-9914-4529-b1f2-6d49a578fca9

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution (k d : ℕ) :
    ∑ j ∈ Ioc k (k + d), 1 / (2 : ℝ) ^ j = 1 / 2 ^ k - 1 / 2 ^ (k + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), ih, pow_succ (2 : ℝ) (k + d)]
    field_simp
    ring
end Formalism.FourierDecayAlt.P.Sz2
