-- Prove2me | solution 1 for D1Bound5.homogeneousMultisetSum_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:56.722476+00:00
-- url     : https://prove2.me/submissions/dc330dd0-ba48-41f3-bd3c-c783aeb20138

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Polynomial Finset

namespace D1Bound5

/-- Reindexing variables preserves the explicit homogeneous multiset sum. -/
theorem _root_.solution
    {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [CommSemiring R]
    (e : ι ≃ κ) (a : κ → R) (n : ℕ) :
    homogeneousMultisetSum (fun i => a (e i)) n = homogeneousMultisetSum a n := by
  unfold homogeneousMultisetSum
  apply Fintype.sum_equiv (Sym.equivCongr e)
  intro t
  simp [Sym.equivCongr, Sym.coe_map, Multiset.map_map]









end D1Bound5
end
