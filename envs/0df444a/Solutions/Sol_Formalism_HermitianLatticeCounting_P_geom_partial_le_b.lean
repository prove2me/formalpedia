-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.geom_partial_le_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:50.578085+00:00
-- url     : https://prove2.me/submissions/c493d833-39cc-431f-9008-5fc8710b24b1

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (M : ℕ) :
    ∑ i ∈ range M, x ^ i ≤ 1 / (1 - x) := by
  rw [one_div, ← tsum_geometric_of_lt_one hx0 hx1]
  exact (summable_geometric_of_lt_one hx0 hx1).sum_le_tsum _ (fun i _ => pow_nonneg hx0 i)
end Formalism.HermitianLatticeCounting.P
