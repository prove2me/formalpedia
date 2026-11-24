-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.lev_mm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:44:24.490601+00:00
-- url     : https://prove2.me/submissions/1f21442b-ad5e-4ac4-9b98-0d983409e24b

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
theorem _root_.solution (k r' : ℕ) (g : Mat k r') (s t : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' s) (levPos k 1 r' t) = g s t := by
  have hs : s.val ≤ 2 * r' + k := by have := s.isLt; omega
  have ht : t.val ≤ 2 * r' + k := by have := t.isLt; omega
  simp only [ιLev, levPos]
  try split_ifs
  all_goals first | omega | simp [hs, ht]
end Formalism.FourierDecayAlt.P.B2x2
