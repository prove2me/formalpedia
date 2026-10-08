-- Prove2me | solution 1 for CurveSymmetry.genus_congr
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:04.659243+00:00
-- url     : https://prove2.me/submissions/9fb8f9d5-a35d-45e4-9680-fe0d4ef4fce2

-- Solution generated from lean/FunctionFieldGenus.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Valuation.ValuationSubring

section
open CurveSymmetry
set_option autoImplicit false
variable {K L : Type*} [Field K] [Algebra ℂ K] [Field L] [Algebra ℂ L]
theorem solution (e : K ≃ₐ[ℂ] L) : genus K = genus L :=
  (holomorphicSpaceEquiv e).finrank_eq
end

#print axioms solution
