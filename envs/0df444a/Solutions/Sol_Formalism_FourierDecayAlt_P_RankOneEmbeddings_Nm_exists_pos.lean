-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm.exists_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:40:47.067806+00:00
-- url     : https://prove2.me/submissions/3291aa51-1c01-4e2e-ae5d-75ac55661d57

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm
theorem _root_.solution {k r : ℕ} (μ : Measure (Mt k r)) (h0 : μ ≠ 0) : ∃ K : Set (Mt k r), IsCompact K ∧ μ K ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply h0
  rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
  exact measure_iUnion_null fun n => hcon _ (isCompact_compactCovering _ n)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm
