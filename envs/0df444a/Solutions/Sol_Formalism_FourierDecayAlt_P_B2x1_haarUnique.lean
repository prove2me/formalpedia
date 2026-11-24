-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.haarUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:46:38.490894+00:00
-- url     : https://prove2.me/submissions/5f77af30-29e9-4812-a0e8-c6daee47aaff

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_exists_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_map_pull
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_pull_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_pull_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution : HaarUnique := by
  intro k r U μ ν hU hμ hν0 hνl hνc
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ hμ.left
  have : (pull hU ν).IsMulLeftInvariant := pull_left ν hνl
  have : IsFiniteMeasureOnCompacts (pull hU μ) := pull_fin μ hμ.finite_compact
  have : IsFiniteMeasureOnCompacts (pull hU ν) := pull_fin ν hνc
  have h0 : pull hU μ ≠ 0 := by
    intro h
    apply hμ.ne_zero
    rw [← map_pull (hU := hU) μ hμ.conc, h, Measure.map_zero]
  obtain ⟨K, hK, hK0⟩ := exists_pos (pull hU μ) h0
  have : (pull hU μ).IsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK hK0
  have : (pull hU μ).IsHaarMeasure := {}
  refine ⟨Measure.haarScalarFactor (pull hU ν) (pull hU μ), ?_⟩
  calc ν = (pull hU ν).map inc := (map_pull ν hν0).symm
    _ = (Measure.haarScalarFactor (pull hU ν) (pull hU μ) • pull hU μ).map inc := by
        rw [← Measure.isMulLeftInvariant_eq_smul (pull hU ν) (pull hU μ)]
    _ = Measure.haarScalarFactor (pull hU ν) (pull hU μ) • μ := by
        rw [Measure.map_smul, map_pull μ hμ.conc]
end Formalism.FourierDecayAlt.P.B2x1
