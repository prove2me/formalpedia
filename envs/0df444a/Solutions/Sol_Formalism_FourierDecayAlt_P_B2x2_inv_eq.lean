-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:47:33.1787+00:00
-- url     : https://prove2.me/submissions/9347a03b-44a0-4dfc-962d-6e6898628014

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
theorem _root_.solution {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) : x⁻¹ = (x.det)⁻¹ • x.adjugate := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
end Formalism.FourierDecayAlt.P.B2x2
