-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.dimN_eq_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:08.441131+00:00
-- url     : https://prove2.me/submissions/676bb695-515c-490d-8a0e-f86015b17858

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
theorem _root_.solution {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) :
    dimN j n0 = 4 * (∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y) + ∑ x, j x ^ 2
      + 2 * (∑ x, j x) * n0 := by
  unfold dimN
  have h1 : ∑ x, ∑ y ∈ univ.filter (fun y => x < y), 2 * j x * j y
      = 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by
    simp only [Finset.mul_sum, mul_assoc]
  have h2 : ∑ x, 2 * j x * n0 = 2 * (∑ x, j x) * n0 := by
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [h1, h2]; ring
end Formalism.HermitianLatticeCounting.P
