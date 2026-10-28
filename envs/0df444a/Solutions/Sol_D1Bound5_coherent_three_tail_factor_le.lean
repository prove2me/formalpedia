-- Prove2me | solution 1 for D1Bound5.coherent_three_tail_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:32:19.959789+00:00
-- url     : https://prove2.me/submissions/e317d191-9a43-4029-be48-e3863141e44a

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset

noncomputable section

namespace D1Bound5











/-- The exact manuscript error factor at any parameter `H>1`. -/
theorem _root_.solution
    (A P H : ℝ) (hH : 1 < H) (hAP : H ≤ A*P) :
    1/(1-1/(A*P))^3-1 ≤ (H/(H-1))^3-1 := by
  have hH0 : 0 < H := by linarith
  have hHm : 0 < H-1 := by linarith
  have hinv : 1/(A*P) ≤ 1/H := one_div_le_one_div_of_le hH0 hAP
  have hbase : (H-1)/H ≤ 1-1/(A*P) := by
    have heq : (H-1)/H = 1-1/H := by field_simp
    rw [heq]
    linarith
  have hbase3 : ((H-1)/H)^3 ≤ (1-1/(A*P))^3 := by gcongr
  have h := one_div_le_one_div_of_le (by positivity : 0 < ((H-1)/H)^3) hbase3
  have heq : 1/((H-1)/H)^3 = (H/(H-1))^3 := by field_simp
  rw [heq] at h
  linarith





end D1Bound5
end
