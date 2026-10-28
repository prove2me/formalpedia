-- Prove2me | solution 1 for D1Bound5.homogeneousMultisetSum_option_succ
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:16.00305+00:00
-- url     : https://prove2.me/submissions/d0cc1702-8578-4097-8334-734e167a3404

import Mathlib.Data.Sym.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Finset Multiset Sym

namespace D1Bound5





/-- When a new variable is adjoined, the complete homogeneous polynomial
satisfies a one-step recursion at every positive degree. -/
theorem _root_.solution
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (a : Option ι → R) (n : ℕ) :
    homogeneousMultisetSum a (n + 1) =
      a none * homogeneousMultisetSum a n +
        homogeneousMultisetSum (fun i : ι => a (some i)) (n + 1) := by
  unfold homogeneousMultisetSum
  calc
    (∑ t : Sym (Option ι) (n + 1), (t.1.map a).prod) =
      ∑ t : Sum (Sym (Option ι) n) (Sym ι (n + 1)),
        (((symOptionSuccEquiv (α := ι)).symm t).1.map a).prod := by
          apply Fintype.sum_equiv (symOptionSuccEquiv (α := ι))
          intro t
          simp
    _ = _ := by
      simp only [Fintype.sum_sum_type]
      simp [symOptionSuccEquiv, SymOptionSuccEquiv.decode,
        Sym.coe_cons, Sym.coe_map, Multiset.map_cons, Multiset.map_map,
        Multiset.prod_cons, Finset.mul_sum]









end D1Bound5
end
