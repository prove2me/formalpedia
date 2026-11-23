-- Prove2me | solution 1 for Formalism.DivisionValues.DivisorInequalityBounds.recAux
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:38.847008+00:00
-- url     : https://prove2.me/submissions/b35b7d4d-27a7-4e91-9d89-73b6ebcf0cbc

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_WeightedPlaceLogSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.DivisorInequalityBounds
namespace Formalism.DivisionValues.DivisorInequalityBounds
theorem _root_.solution (X B0 Nc m C0 ce Eb lx2 A : ℝ) (hX : 0 < X) (hNc : 0 ≤ Nc)
    (hC0 : 1 ≤ C0) (hce : C0 ≤ ce) (hl : 0 ≤ lx2) (hEb : Eb ≤ ce * m * (X * B0 + lx2 * Nc)) :
    0 ≤ lx2 * Nc / X ∧ X ≤ ce / C0 * X ∧ Eb ≤ C0 * m * (ce / C0 * X) * (B0 + lx2 * Nc / X) ∧
    (50 * C0 + 10) * (A + m * (B0 + lx2 * Nc / X) * (ce / C0 * X)) =
      (50 * C0 + 10) * A + (50 * C0 + 10) * (ce / C0) * (m * (X * B0 + lx2 * Nc)) := by
  have hC : 0 < C0 := by linarith
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · have : 1 ≤ ce / C0 := by rw [le_div_iff₀ hC]; linarith
    nlinarith
  · have : C0 * m * (ce / C0 * X) * (B0 + lx2 * Nc / X) = ce * m * (X * B0 + lx2 * Nc) := by
      field_simp
    rw [this]; exact hEb
  · field_simp
end Formalism.DivisionValues.DivisorInequalityBounds
