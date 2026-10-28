-- Prove2me | solution 1 for D1Bound5.full_ring_one_three_common_extension_is_integer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:21.46804+00:00
-- url     : https://prove2.me/submissions/c116f5ea-e59e-473e-ac76-2047ddd161fa

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_one_three_common_extension_is_integer

section
open scoped NumberField ComplexConjugate
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]









/-- The rationality assertion of lem:pr-one-three in the full integer ring
of every imaginary quadratic field, with no coordinate-model assumption. -/
theorem _root_.solution (hK : finrank ℚ K = 2)
    {z : 𝓞 K} (hr : ∃ r : 𝓞 K, r*r = z+1)
    (hs : ∃ s : 𝓞 K, s*s = 3*z+1) : ∃ n : ℤ, z = (n : 𝓞 K) := by
  obtain ⟨tau, nu, _, hd, ⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  have hr' : ∃ r : QuadInt tau nu, r*r = e.symm z+1 := by
    obtain ⟨r, hr⟩ := hr
    refine ⟨e.symm r, ?_⟩
    simpa only [map_mul, map_add, map_one] using congrArg e.symm hr
  have hs' : ∃ s : QuadInt tau nu, s*s = 3*e.symm z+1 := by
    obtain ⟨s, hs⟩ := hs
    refine ⟨e.symm s, ?_⟩
    simpa only [map_mul, map_add, map_one, map_ofNat] using congrArg e.symm hs
  obtain ⟨n, hn⟩ := one_three_common_extension_is_integer tau nu hd hr' hs'
  refine ⟨n, ?_⟩
  simpa only [RingEquiv.apply_symm_apply, map_intCast] using congrArg e hn

end D1Bound5
end
