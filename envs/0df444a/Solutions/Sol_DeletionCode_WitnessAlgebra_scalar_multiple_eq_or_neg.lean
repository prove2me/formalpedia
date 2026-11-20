-- Prove2me | solution 1 for DeletionCode.WitnessAlgebra.scalar_multiple_eq_or_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:08.671245+00:00
-- url     : https://prove2.me/submissions/81d682cf-f228-4af1-a876-62efa3091c46

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
import Theorems.Thm_DeletionCode_WitnessAlgebra_scalar_eq_one_or_neg_one

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessAlgebra
theorem _root_.solution {H : Type*} (g w : H → ℚ) (a : ℚ)
    (hg : SignedUnitVector g) (hw : SignedUnitVector w)
    (hg0 : g ≠ 0) (ha : a ≠ 0) (hrel : w = a • g) : w = g ∨ w = -g := by
  rcases scalar_eq_one_or_neg_one g w a hg hw hg0 ha hrel with h | h
  · left; simpa [h] using hrel
  · right; simpa [h] using hrel
end DeletionCode.WitnessAlgebra
