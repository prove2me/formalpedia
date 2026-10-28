-- Prove2me | solution 1 for D1Bound5.lagrange_power_moment_eq_hsymm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:22.033856+00:00
-- url     : https://prove2.me/submissions/cdaca7b5-96bd-4098-ab51-42a48e2b3773

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_eq_hsymm
import Theorems.Thm_D1Bound5_lagrange_power_moment_eq_homogeneousMultisetSum

section
open Polynomial Finset

namespace D1Bound5









/-- All-order Lagrange moments equal mathlib's complete homogeneous
symmetric polynomials, with no nonzero-node restriction. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (hinj : Set.InjOn a s) (k : ℕ) :
    (∑ i ∈ s, (a i) ^ (s.card - 1 + k) /
      (∏ j ∈ s.erase i, (a i - a j))) =
      MvPolynomial.aeval (fun i : s => a i) (MvPolynomial.hsymm s F k) := by
  rw [← homogeneousMultisetSum_eq_hsymm]
  exact lagrange_power_moment_eq_homogeneousMultisetSum s a hs hinj k

end D1Bound5
end
