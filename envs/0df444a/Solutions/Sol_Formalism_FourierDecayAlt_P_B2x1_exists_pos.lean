-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.exists_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:11:52.585478+00:00
-- url     : https://prove2.me/submissions/9599810a-0822-457d-8c20-8393539742c2

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible

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
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X] [MeasurableSpace X] (μ : Measure X) (h0 : μ ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ K ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h0
  have : μ Set.univ = 0 := by
    rw [← iUnion_compactCovering X]
    exact measure_iUnion_null (fun n => hcon _ (isCompact_compactCovering _ n))
  exact Measure.measure_univ_eq_zero.mp this
end Formalism.FourierDecayAlt.P.B2x1
