-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:49:24.264112+00:00
-- url     : https://prove2.me/submissions/5e9ecee3-5c59-40c0-968c-fd6d50225cf0

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution (KW : CompactW) {z : Vc k r} (hz : inWb k r z) (hT : 0 < Tz k r z) {μW : Measure (Mt k r)}
    (hW : IsHaarOn (UWset k r z) μW) : IsFiniteMeasure μW := by
  have hK : IsCompact (UWset k r z) := KW k r z hz hT
  constructor
  have h1 := hW.finite_compact _ hK
  calc μW Set.univ ≤ μW (UWset k r z) + μW (UWset k r z)ᶜ := measure_univ_le_add_compl _
    _ < ∞ := by rw [hW.conc, add_zero]; exact h1
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
