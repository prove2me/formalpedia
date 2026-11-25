-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.Phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:30.233464+00:00
-- url     : https://prove2.me/submissions/1447d0dd-b08e-46b8-a18d-4d3607cc33fa

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
theorem _root_.solution (s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : ℂ × (Mt k r × Mt k r)) :
    Phi s x = (Matrix.of x.2.1 : Mat k r)⁻¹ * embWb k r (s x.1) * Matrix.of x.2.2 := rfl
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
