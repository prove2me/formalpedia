-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.ae_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:43.451102+00:00
-- url     : https://prove2.me/submissions/a738b27a-e1d3-42f3-9456-539bbe87b527

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
theorem _root_.solution {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ x : Mt k r ∂μ, (Matrix.of x : Mat k r) ∈ U := by
  exact ae_iff.2 h.conc
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
