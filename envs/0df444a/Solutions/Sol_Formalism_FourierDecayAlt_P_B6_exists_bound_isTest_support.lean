-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.exists_bound_isTest_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:06:01.450128+00:00
-- url     : https://prove2.me/submissions/b37c6bcb-8d86-4347-a4e4-20f038a5f998

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {w : ℝ → ℝ} (h : IsTest w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, w τ ≠ 0 → 0 < τ ∧ max 1 (τ ^ 2)⁻¹ ≤ M := by
  obtain ⟨_, hc, hs⟩ := h
  have hcont : ContinuousOn (fun τ : ℝ => (τ ^ 2)⁻¹) (tsupport w) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro τ hτ
    have : 0 < τ := hs hτ
    positivity
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn hcont
  refine ⟨max 1 M, le_trans zero_le_one (le_max_left _ _), fun τ hτ => ?_⟩
  have hmem : τ ∈ tsupport w := subset_tsupport _ hτ
  refine ⟨hs hmem, ?_⟩
  have := hM τ hmem
  rw [Real.norm_eq_abs] at this
  exact max_le_max le_rfl ((le_abs_self _).trans this)
end Formalism.FourierDecayAlt.P.B6
