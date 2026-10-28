-- Prove2me | solution 1 for D1Bound5.coherent_three_quotient_forms_not_both_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:58.723028+00:00
-- url     : https://prove2.me/submissions/5612afc5-e517-4dca-baf0-89ab48d69e9b

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_CoherentThreeNonvanishing_Definitions
import Theorems.Thm_D1Bound5_coherentQuotientForm_three_eq
import Theorems.Thm_D1Bound5_coherent_analytic_anchor_root_sq
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
import Theorems.Thm_D1Bound5_coherent_two_three_forms_not_both_zero

section
open Finset

namespace D1Bound5













/-- Simultaneous nonvanishing for the actual two coherent quotient
forms.  The chosen analytic roots supply all square identities; the
remaining hypotheses are precisely distinctness, ordering and size. -/
theorem _root_.solution
    (a : Fin 4 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ)
    (heta : eta^2 = p*q)
    (hA : 1 ≤ ‖a 0‖) (hAB : ‖a 0‖ ≤ ‖a 1‖)
    (hBS : ‖a 1‖ ≤ ‖a 2‖) (hST : ‖a 2‖ ≤ ‖a 3‖)
    (hTP : ‖a 3‖ ≤ ‖p‖) (hPQ : ‖p‖ ≤ ‖q‖)
    (hsize : 32*‖a 1‖*‖a 2‖*‖a 3‖/‖a 0‖^3 ≤ ‖p‖^2) :
    coherentQuotientForm (coherentTriple012 a)
      (coherentVandermonde3 (coherentTriple012 a)) p q eta ≠ 0 ∨
    coherentQuotientForm (coherentTriple013 a)
      (coherentVandermonde3 (coherentTriple013 a)) p q eta ≠ 0 := by
  have hinj2 : Function.Injective (coherentTriple012 a) :=
    hinj.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 4))
  have hinj3 : Function.Injective (coherentTriple013 a) :=
    hinj.comp (by decide : Function.Injective (![0,1,3] : Fin 3 → Fin 4))
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    fin_cases i
    · exact norm_pos_iff.mp (by linarith : 0 < ‖a 0‖)
    · exact norm_pos_iff.mp (by linarith : 0 < ‖a 1‖)
    · exact norm_pos_iff.mp (by linarith : 0 < ‖a 2‖)
    · exact norm_pos_iff.mp (by linarith : 0 < ‖a 3‖)
  have hp : p ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖p‖)
  have hq : q ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖q‖)
  let z := coherentTerminalRoot p q eta
  let R : Fin 4 → ℂ := fun i => coherentAnchorRoot (a i) p q eta
  have hz : z^2 = p*q+1 := coherent_analytic_terminal_root_sq p q eta hp hq heta
  have hR : ∀ i, (R i)^2 = (a i*p+1)*(a i*q+1) := fun i =>
    coherent_analytic_anchor_root_sq (a i) p q eta (ha i) hp hq heta
  have h := coherent_two_three_forms_not_both_zero a R hinj p q z hz hR
    hA hAB hBS hST hTP hPQ hsize
  rw [coherentQuotientForm_three_eq _ hinj2, coherentQuotientForm_three_eq _ hinj3]
  simpa [coherentTriple012, coherentTriple013, R, z] using h

end D1Bound5
end
