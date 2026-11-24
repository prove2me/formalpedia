-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.fs_sizes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:48.525553+00:00
-- url     : https://prove2.me/submissions/65f46412-e9e6-4bc5-833a-2132a1962475

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (C m M6 Q L kR lam : ℝ) (hC : 1 ≤ C) (hM64 : 64 ≤ M6) (hmM : m * m ≤ M6)
    (hQ : 0 ≤ Q) (hL2 : 1 / 2 ≤ L) (hk0 : 0 ≤ kR) (hlk : lam ≤ kR)
    (hyp : (16 * C + Q * Q) * M6 * L ≤ kR * lam) :
    8 ≤ kR ∧ m ≤ kR ∧ Q ≤ kR ∧ M6 ≤ 2 * (M6 * L) ∧ 16 * (M6 * L) ≤ kR * lam ∧
      16 * C * (M6 * L) ≤ kR * lam := by
  have hM0 : 0 ≤ M6 := by linarith
  have hmE : M6 ≤ 2 * (M6 * L) := by
    have := mul_le_mul_of_nonneg_left hL2 hM0
    linarith
  have hE32 : 32 ≤ M6 * L := by linarith
  have hE0 : 0 ≤ M6 * L := by linarith
  have hQQ : 0 ≤ Q * Q * (M6 * L) := mul_nonneg (mul_nonneg hQ hQ) hE0
  have hCE0 : M6 * L ≤ C * (M6 * L) := le_mul_of_one_le_left hE0 hC
  have e : (16 * C + Q * Q) * M6 * L = 16 * (C * (M6 * L)) + Q * Q * (M6 * L) := by ring
  rw [e] at hyp
  have hkk : kR * lam ≤ kR * kR := mul_le_mul_of_nonneg_left hlk hk0
  have hQ32 : Q * Q ≤ Q * Q * (M6 * L) := le_mul_of_one_le_right (mul_nonneg hQ hQ) (by linarith)
  refine ⟨?_, ?_, ?_, hmE, by linarith, by linarith⟩
  · by_contra h
    have h' : kR < 8 := not_le.1 h
    have := mul_self_lt_mul_self hk0 h'
    linarith
  · by_contra h
    have h' : kR < m := not_le.1 h
    have := mul_self_lt_mul_self hk0 h'
    linarith
  · by_contra h
    have h' : kR < Q := not_le.1 h
    have := mul_self_lt_mul_self hk0 h'
    linarith
end Formalism.HermitianLatticeCounting.P
