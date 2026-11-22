-- Prove2me | solution 1 for Formalism.vM_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:03:57.690472+00:00
-- url     : https://prove2.me/submissions/c9a80752-3642-403a-82ba-a6c31d39e943

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution : ∀ n : ℕ, |(Λ n : ℝ)| ≤ 1 * Λ n := fun n => by
  rw [one_mul, abs_of_nonneg vonMangoldt_nonneg]
end Formalism
