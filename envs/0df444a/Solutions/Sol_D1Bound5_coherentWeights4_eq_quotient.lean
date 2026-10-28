-- Prove2me | solution 1 for D1Bound5.coherentWeights4_eq_quotient
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:16.811687+00:00
-- url     : https://prove2.me/submissions/b3a6fbd6-6a01-4b33-b8f6-7b12b02c5f9d

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
    {F : Type*} [Field F] (a : Fin 4 → F) (hinj : Function.Injective a)
    (i : Fin 4) :
    coherentWeights4 a i = coherentVandermonde4 a * (a i) ^ (4 - 2) /
      (∏ j ∈ Finset.univ.erase i, (a i - a j)) := by
  have hne (i j : Fin 4) (hij : i ≠ j) : a i - a j ≠ 0 :=
    sub_ne_zero.mpr (hinj.ne hij)
  have h01 := hne 0 1 (by decide)
  have h02 := hne 0 2 (by decide)
  have h03 := hne 0 3 (by decide)
  have h10 := hne 1 0 (by decide)
  have h12 := hne 1 2 (by decide)
  have h13 := hne 1 3 (by decide)
  have h20 := hne 2 0 (by decide)
  have h21 := hne 2 1 (by decide)
  have h23 := hne 2 3 (by decide)
  have h30 := hne 3 0 (by decide)
  have h31 := hne 3 1 (by decide)
  have h32 := hne 3 2 (by decide)
  have he0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} := by decide
  have he1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
  have he2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} := by decide
  have he3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0, 1, 2} := by decide
  fin_cases i <;>
    simp [coherentWeights4, coherentVandermonde4, he0, he1, he2, he3] <;>
    field_simp [h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32] <;> ring













end D1Bound5
end
