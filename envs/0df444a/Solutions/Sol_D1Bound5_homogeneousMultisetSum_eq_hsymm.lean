-- Prove2me | solution 1 for D1Bound5.homogeneousMultisetSum_eq_hsymm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:30.004383+00:00
-- url     : https://prove2.me/submissions/bf951512-c9db-465b-a5ce-837e210e0989

import Mathlib.Data.Sym.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Finset Multiset Sym

namespace D1Bound5



/-- The multiset sum agrees at every degree with mathlib's hsymm under evaluation. -/
theorem _root_.solution
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (a : ι → R) (n : ℕ) :
    homogeneousMultisetSum a n =
      MvPolynomial.aeval a (MvPolynomial.hsymm ι R n) := by
  simp only [homogeneousMultisetSum, MvPolynomial.hsymm, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, MvPolynomial.aeval_X]











end D1Bound5
end
