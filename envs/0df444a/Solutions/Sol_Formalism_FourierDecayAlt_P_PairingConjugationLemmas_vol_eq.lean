-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PairingConjugationLemmas.vol_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:17.482518+00:00
-- url     : https://prove2.me/submissions/62b2d438-183f-4a04-8ed9-4f80158568d1

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PairingTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PairingConjugationLemmas
open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison
noncomputable section
variable {f : ℕ}
variable (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]
namespace Formalism.FourierDecayAlt.P.PairingConjugationLemmas
theorem _root_.solution : ∃ c : NNReal, 0 < c ∧
    (volume : Measure (V f)) = c • Measure.map (Tl La) (volume : Measure (Fin (finrank ℤ La) → ℝ)) := by
  haveI : (Measure.map (Tl La) (volume : Measure (Fin (finrank ℤ La) → ℝ))).IsAddHaarMeasure :=
    (Tl La).isAddHaarMeasure_map _
  exact ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    Measure.isAddLeftInvariant_eq_smul _ _⟩
end Formalism.FourierDecayAlt.P.PairingConjugationLemmas
