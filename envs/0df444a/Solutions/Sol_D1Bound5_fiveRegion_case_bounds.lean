-- Prove2me | solution 1 for D1Bound5.fiveRegion_case_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:40:13.277234+00:00
-- url     : https://prove2.me/submissions/a0544bb3-c256-475c-8926-0c79e8badbab

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_CoupledPhaseBounds_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_FiveRegionParameters_Definitions
import Theorems.Thm_D1Bound5_fiveRegion_parameters

section
noncomputable section

namespace D1Bound5






















theorem fiveRegion_Q_reciprocal (r : Fin 5) : 1/fiveRegionQ r=fiveRegionAnchorRatio r := by
  fin_cases r <;> norm_num [fiveRegionQ,fiveRegionAnchorRatio]



theorem _root_.solution (r : Fin 5) (A B : ℝ)
    (hA0 : 0 ≤ A) (hA8 : A^2 ≤ 8) (hc : FiveRegionCase r A B) :
    fiveRegionMinNorm r ≤ A^2 ∧ A ≤ fiveRegionMaxA r ∧
      fiveRegionMinB r ≤ B ∧ 3 ≤ B ∧
      fiveRegionQ r*A ≤ B ∧ A ≤ fiveRegionAnchorRatio r*B := by
  have hN : fiveRegionMinNorm r ≤ A^2 := by
    have hs := hc.1
    by_cases h4 : r=4
    · rw [if_pos h4] at hs
      subst r
      exact hs
    · rw [if_neg h4] at hs
      exact hs.ge
  have hupper : A ≤ fiveRegionMaxA r := by
    fin_cases r
    · change A ≤ 1
      have hs : A^2 = 1 := by
        have hh := hc.1
        change (if (0 : Fin 5)=4 then 5 ≤ A^2 else A^2=1) at hh
        rw [if_neg (by decide : (0 : Fin 5) ≠ 4)] at hh
        exact hh
      nlinarith only [hA0,hs]
    · change A ≤ 3/2
      have hs : A^2 = 2 := by
        have hh := hc.1
        change (if (1 : Fin 5)=4 then 5 ≤ A^2 else A^2=2) at hh
        rw [if_neg (by decide : (1 : Fin 5) ≠ 4)] at hh
        exact hh
      nlinarith only [hA0,hs]
    · change A ≤ 7/4
      have hs : A^2 = 3 := by
        have hh := hc.1
        change (if (2 : Fin 5)=4 then 5 ≤ A^2 else A^2=3) at hh
        rw [if_neg (by decide : (2 : Fin 5) ≠ 4)] at hh
        exact hh
      nlinarith only [hA0,hs]
    · change A ≤ 2
      have hs : A^2 = 4 := by
        have hh := hc.1
        change (if (3 : Fin 5)=4 then 5 ≤ A^2 else A^2=4) at hh
        rw [if_neg (by decide : (3 : Fin 5) ≠ 4)] at hh
        exact hh
      nlinarith only [hA0,hs]
    · change A ≤ 17/6
      nlinarith only [hA0,hA8]
  have hB : fiveRegionMinB r ≤ B := hc.2
  have hB3 : 3 ≤ B := (fiveRegion_parameters r).1.trans hB
  have hqA : fiveRegionQ r*A ≤ B := by
    fin_cases r <;> norm_num [fiveRegionMaxA,fiveRegionMinB,fiveRegionQ] at hupper hB ⊢
    all_goals linarith only [hupper,hB]
  have hq0 : 0 < fiveRegionQ r := lt_of_lt_of_le (by norm_num) (fiveRegion_parameters r).2.2.2.1
  refine ⟨hN,hupper,hB,hB3,hqA,?_⟩
  rw [← fiveRegion_Q_reciprocal]
  calc
    A ≤ B/fiveRegionQ r := (le_div_iff₀ hq0).mpr (by simpa only [mul_comm] using hqA)
    _ = (1/fiveRegionQ r)*B := by ring

end D1Bound5
end
