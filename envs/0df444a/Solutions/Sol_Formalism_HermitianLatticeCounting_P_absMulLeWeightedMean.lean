-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.absMulLeWeightedMean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:23.216687+00:00
-- url     : https://prove2.me/submissions/7d12f399-e755-4afa-a1d1-f5a52162b8e1

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : WeightedAMGM := by
  intro a b La hLa
  have hL0 : La ≠ 0 := hLa.ne'
  obtain ⟨t, ht⟩ : ∃ t, t = |b| / La := ⟨_, rfl⟩
  have hbt : |b| = La * t := by rw [ht]; first | (field_simp; ring) | field_simp
  have hb2 : b ^ 2 = La ^ 2 * t ^ 2 := by rw [← sq_abs b, hbt]; ring
  have hb2' : b ^ 2 / La = La * t ^ 2 := by
    rw [hb2, div_eq_iff hL0]; ring
  rw [abs_mul, hbt, hb2', ← sq_abs a]
  nlinarith [mul_nonneg hLa.le (sq_nonneg (|a| - t))]
end Formalism.HermitianLatticeCounting.P
