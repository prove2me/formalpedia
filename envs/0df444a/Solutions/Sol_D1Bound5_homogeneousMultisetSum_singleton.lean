-- Prove2me | solution 1 for D1Bound5.homogeneousMultisetSum_singleton
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:40.098986+00:00
-- url     : https://prove2.me/submissions/b422efba-3c27-409d-a91b-fc963df903ae

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Polynomial Finset

namespace D1Bound5





/-- A single variable has exactly one monomial in each degree. -/
theorem _root_.solution
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (a : ι → R) (t : ι) (n : ℕ) :
    homogeneousMultisetSum (fun i : ({t} : Finset ι) => a i) n = (a t)^n := by
  let t' : ({t} : Finset ι) := ⟨t, Finset.mem_singleton_self t⟩
  let : Unique ({t} : Finset ι) :=
    { default := t', uniq := fun i => Subtype.ext (Finset.mem_singleton.mp i.2) }
  have hp (v : Sym ({t} : Finset ι) n) :
      (v.1.map (fun i : ({t} : Finset ι) => a i)).prod = (a t)^n := by
    rw [Sym.eq_replicate_of_subsingleton t' v]
    simp [Sym.replicate, t']
  simp only [homogeneousMultisetSum, Fintype.sum_unique]
  exact hp default





end D1Bound5
end
