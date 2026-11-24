-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.mulM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:44:26.033834+00:00
-- url     : https://prove2.me/submissions/f8978be7-f15f-4e29-b76e-e81cf4f9411d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution {k r : ℕ} : Continuous (mulM : Mt k r × Mt k r → Mt k r) := by
  have h1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  have h2 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  show Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r))
  exact h1.matrix_mul h2
end Formalism.FourierDecayAlt.P.B2x2
