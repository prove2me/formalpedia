-- Prove2me | solution 1 for D1Bound5.coherentWeights2_eq_quotient
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:17.303601+00:00
-- url     : https://prove2.me/submissions/bf4f9dee-55dd-483e-b8cc-b94fb7d75627

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
    {F : Type*} [Field F] (a : Fin 2 → F) (hinj : Function.Injective a)
    (i : Fin 2) :
    coherentWeights2 a i = coherentVandermonde2 a * (a i) ^ (2 - 2) /
      (∏ j ∈ Finset.univ.erase i, (a i - a j)) := by
  have h01 : a 0 - a 1 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have h10 : a 1 - a 0 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have he0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have he1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  fin_cases i <;>
    simp [coherentWeights2, coherentVandermonde2, he0, he1] <;>
    field_simp [h01, h10] <;> ring

















end D1Bound5
end
