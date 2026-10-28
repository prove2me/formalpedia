-- Prove2me | solution 1 for D1Bound5.homogeneousMultisetSum_insert
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:04.656872+00:00
-- url     : https://prove2.me/submissions/e24ab4d6-9a3a-4cfe-8093-923c1137a889

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_equiv
import Theorems.Thm_D1Bound5_homogeneousMultisetSum_option_succ

section
open Polynomial Finset

namespace D1Bound5



/-- Finite-set variable adjunction, compatible with barycentric interpolation. -/
theorem _root_.solution
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (a : ι → R) (t : ι) (ht : t ∉ s) (n : ℕ) :
    homogeneousMultisetSum (fun i : (insert t s : Finset ι) => a i) (n + 1) =
      a t * homogeneousMultisetSum (fun i : (insert t s : Finset ι) => a i) n +
        homogeneousMultisetSum (fun i : s => a i) (n + 1) := by
  let e := Finset.subtypeInsertEquivOption ht
  let b : Option s → R := fun o => a (e.symm o)
  have hre (k : ℕ) : homogeneousMultisetSum b k =
      homogeneousMultisetSum (fun i : (insert t s : Finset ι) => a i) k :=
    homogeneousMultisetSum_equiv e.symm (fun i => a i) k
  have h := homogeneousMultisetSum_option_succ b n
  rw [hre (n + 1), hre n] at h
  exact h







end D1Bound5
end
