-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.haar_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:06:06.554594+00:00
-- url     : https://prove2.me/submissions/4fc04eab-9f09-4c36-98f1-5ee07a4d219c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (HU : HaarUnique) {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn U μ) (hν : IsHaarOn U ν) : ∃ a : ℝ≥0, 0 < a ∧ ν = a • μ := by
  obtain ⟨c, hc⟩ := HU k r U μ ν hU hμ hν.conc hν.left hν.finite_compact
  refine ⟨c, ?_, hc⟩
  rcases eq_or_ne c 0 with h0 | h0
  · exact absurd (by rw [hc, h0, zero_smul]) hν.ne_zero
  · exact pos_iff_ne_zero.2 h0
end Formalism.FourierDecayAlt.P.LongWeylElement
