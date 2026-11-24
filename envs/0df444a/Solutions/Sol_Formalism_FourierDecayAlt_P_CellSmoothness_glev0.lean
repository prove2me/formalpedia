-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CellSmoothness.glev0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:50.468815+00:00
-- url     : https://prove2.me/submissions/ba2c7429-d91c-4e6b-88be-07cceb7b8ddf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CellSmoothness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CellSmoothness
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CellSmoothness
theorem _root_.solution {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Formalism.FourierDecayAlt.Q.Glev k r 0 := by simpa [Formalism.FourierDecayAlt.Q.Glev] using hg
end Formalism.FourierDecayAlt.P.CellSmoothness
