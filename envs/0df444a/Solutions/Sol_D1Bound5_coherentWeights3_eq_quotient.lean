-- Prove2me | solution 1 for D1Bound5.coherentWeights3_eq_quotient
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:36.669722+00:00
-- url     : https://prove2.me/submissions/3075d22b-7619-4a33-8816-526a308527d5

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions

section
open Finset

namespace D1Bound5















theorem _root_.solution
    {F : Type*} [Field F] (a : Fin 3 → F) (hinj : Function.Injective a)
    (i : Fin 3) :
    coherentWeights3 a i = coherentVandermonde3 a * (a i) ^ (3 - 2) /
      (∏ j ∈ Finset.univ.erase i, (a i - a j)) := by
  have hne (i j : Fin 3) (hij : i ≠ j) : a i - a j ≠ 0 :=
    sub_ne_zero.mpr (hinj.ne hij)
  have h01 := hne 0 1 (by decide)
  have h02 := hne 0 2 (by decide)
  have h10 := hne 1 0 (by decide)
  have h12 := hne 1 2 (by decide)
  have h20 := hne 2 0 (by decide)
  have h21 := hne 2 1 (by decide)
  have he0 : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  have he1 : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have he2 : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  fin_cases i <;>
    simp [coherentWeights3, coherentVandermonde3, he0, he1, he2] <;>
    field_simp [h01, h02, h10, h12, h20, h21] <;> ring















end D1Bound5
end
