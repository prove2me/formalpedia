-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.lev_mn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:45:02.693992+00:00
-- url     : https://prove2.me/submissions/aa48657b-8d48-47a1-a08c-0aa1390a0cea

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
theorem _root_.solution (k r' : ℕ) (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : mid k r' p) (hq : ¬ mid k r' q) :
    ιLev k 1 r' g p q = 0 := by
  have hp' : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 := hp
  have hq' : ¬ (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) := hq
  simp only [ιLev]
  split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.P.B2x2
