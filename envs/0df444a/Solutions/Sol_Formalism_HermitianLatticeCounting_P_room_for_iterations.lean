-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.room_for_iterations
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:44.830497+00:00
-- url     : https://prove2.me/submissions/83ca0c2b-ba0c-4102-b6e4-65eeed8c89c9

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
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : StepsRoom := by
  intro n q f P b hq
  constructor
  · have : n^2*f ≤ P0 n q f := by
      unfold P0
      calc n^2*f = 1 * (n^2*f) := by ring
        _ ≤ (8*q) * (n^2*f) := Nat.mul_le_mul_right _ (by omega)
        _ = 8*q*n^2*f := by ring
    omega
  · intro hP
    unfold b1
    have h1 : (P:ℝ) ≤ 2 * (P0 n q f : ℝ) := by exact_mod_cast hP
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1 hn]
end Formalism.HermitianLatticeCounting.P
