-- Prove2me | solution 1 for Formalism.HF.P.apld_nonprime_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:58.061908+00:00
-- url     : https://prove2.me/submissions/dbdb50d9-f499-4eb9-bf0e-3365183d6d97

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
variable {q : ℕ} [NeZero q] {a : ZMod q}
namespace Formalism.HF.P
theorem _root_.solution (a : ZMod q) (x : ℝ) (n : ℕ) :
    0 ≤ (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x := by
  split_ifs
  · simp
  · exact div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)
end Formalism.HF.P
