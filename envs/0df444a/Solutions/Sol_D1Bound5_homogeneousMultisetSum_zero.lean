-- Prove2me | solution 1 for D1Bound5.homogeneousMultisetSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:07.58288+00:00
-- url     : https://prove2.me/submissions/9c5a466e-e08e-4e62-9b6b-47d45d980b58

import Mathlib.Data.Sym.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_eq_hsymm

section
open Finset Multiset Sym

namespace D1Bound5







/-- The empty-degree complete homogeneous symmetric polynomial evaluates to one. -/
@[simp] theorem _root_.solution
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (a : ι → R) : homogeneousMultisetSum a 0 = 1 := by
  rw [homogeneousMultisetSum_eq_hsymm]
  simp







end D1Bound5
end
