-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.coeff_prod_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:00.660559+00:00
-- url     : https://prove2.me/submissions/c7e64e11-872e-465d-b27c-a427f89271bc

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Polynomial Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] (f : ι → R)
    (J : Finset ι) :
    (∏ j ∈ J, (1 + X * C (f j))).coeff 0 = 1 ∧
    (∏ j ∈ J, (1 + X * C (f j))).coeff 1 = ∑ j ∈ J, f j ∧
    2 * (∏ j ∈ J, (1 + X * C (f j))).coeff 2 = (∑ j ∈ J, f j) ^ 2 - ∑ j ∈ J, f j ^ 2 := by
  induction J using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a J ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    rw [prod_insert ha, sum_insert ha, sum_insert ha]
    set P := ∏ j ∈ J, (1 + X * C (f j))
    have key : (1 + X * C (f a)) * P = P + X * (C (f a) * P) := by ring
    rw [key]
    refine ⟨?_, ?_, ?_⟩
    · simp [coeff_add, h0]
    · rw [coeff_add, coeff_X_mul, coeff_C_mul, h0, h1]; ring
    · rw [coeff_add, coeff_X_mul, coeff_C_mul, h1]; linear_combination h2
end Formalism.NuclearRankWeightBounds.P
