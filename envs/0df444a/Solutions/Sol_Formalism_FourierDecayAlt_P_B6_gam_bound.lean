-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.gam_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:47:57.999566+00:00
-- url     : https://prove2.me/submissions/251b49db-8b3f-4c06-9685-b8ee639439a9

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gam_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gam_continuous

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
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2) (ρ : ℝ) : ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ m t, |gam ρ W m t| ≤ Γ := by
  have hb : ∀ m, ∃ C, ∀ t, ‖gam ρ W m t‖ ≤ C := fun m =>
    (gam_continuous hW hWs ρ m).bounded_above_of_compact_support
      (HasCompactSupport.intro (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2))
        fun t ht => gam_zero hWs ρ m fun h => ht ⟨h.1.le, h.2.le⟩)
  obtain ⟨C0, h0⟩ := hb 0
  obtain ⟨C1, h1⟩ := hb 1
  obtain ⟨C2, h2⟩ := hb 2
  refine ⟨max (max C0 C1) C2, ?_, ?_⟩
  · exact le_trans (le_trans (norm_nonneg _) (h2 0)) (le_max_right _ _)
  · intro m t
    match m with
    | 0 => exact le_trans (h0 t) (le_trans (le_max_left _ _) (le_max_left _ _))
    | 1 => exact le_trans (h1 t) (le_trans (le_max_right _ _) (le_max_left _ _))
    | (n + 2) => exact le_trans (h2 t) (le_max_right _ _)
end Formalism.FourierDecayAlt.P.B6
