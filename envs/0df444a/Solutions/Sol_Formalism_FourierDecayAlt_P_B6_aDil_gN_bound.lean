-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.aDil_gN_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:44:57.169074+00:00
-- url     : https://prove2.me/submissions/e13588eb-d1aa-4d71-b84a-c99d1219d767

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_inv_continuousOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (k r : ℕ) {a b : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc a b, gN (aDil k r t) ≤ K ∧ gN (aDil k r t)⁻¹ ≤ K := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun t ht => lt_of_lt_of_le ha ht.1
  obtain ⟨C₁, h₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((gN_continuous.comp_continuousOn (aDil_continuousOn k r)).mono hsub)
  obtain ⟨C₂, h₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((gN_continuous.comp_continuousOn (aDil_inv_continuousOn k r)).mono hsub)
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun t ht => ⟨?_, ?_⟩⟩
  · exact ((le_abs_self _).trans (h₁ t ht)).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact ((le_abs_self _).trans (h₂ t ht)).trans ((le_max_right _ _).trans (le_max_left _ _))
end Formalism.FourierDecayAlt.P.B6
