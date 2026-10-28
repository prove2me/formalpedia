-- Prove2me | solution 1 for D1Bound5.fiveRegion_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:33.017168+00:00
-- url     : https://prove2.me/submissions/a96570e7-5a13-4693-ae5b-1b600a86668b

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

section
noncomputable section

namespace D1Bound5
























theorem _root_.solution (r : Fin 5) :
    3 ≤ fiveRegionMinB r ∧ 1 ≤ fiveRegionMinNorm r ∧
    2 < fiveRegionFrontier r ∧ 1 ≤ fiveRegionQ r ∧
    0 < fiveRegionGap r ∧ 0 < fiveRegionCoupledGap r ∧
    0 < fiveRegionPhase r ∧ 0 < fiveRegionPResidual r ∧
    0 < fiveRegionTriangle r ∧
    (51051/400000 : ℝ)*fiveRegionTriangle r/(fiveRegionMinB r)^2 < 1 ∧
    fiveRegionGap r < fiveRegionRetained r/(fiveRegionTriangle r)^2 ∧
    fiveRegionCoupledGap r < fiveRegionRetained r/((3535/409600 : ℝ)*fiveRegionPhase r) ∧
    finitePAdaptiveRate (1/fiveRegionQ r) < fiveRegionPResidual r ∧
    CoupledPhaseRow (fiveRegionQ r) (fiveRegionPhase r) := by
  fin_cases r <;> norm_num [fiveRegionMinB,fiveRegionMinNorm,fiveRegionFrontier,
    fiveRegionQ,fiveRegionGap,fiveRegionCoupledGap,fiveRegionPhase,fiveRegionPResidual,
    fiveRegionTriangle,fiveRegionRetained,fiveRegionAnchorRatio,finitePAdaptiveRate,CoupledPhaseRow]



end D1Bound5
end
