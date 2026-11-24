-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.lev_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:44:29.472098+00:00
-- url     : https://prove2.me/submissions/8086a166-3d22-4722-9f71-4ba443e7c917

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
theorem _root_.solution (k r' : ℕ) (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : ¬ mid k r' p) :
    ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  have hp' : ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := hp
  simp only [ιLev]
  split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.P.B2x2
