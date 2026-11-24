-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.rmulF_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:49:12.638264+00:00
-- url     : https://prove2.me/submissions/d146be04-bef6-43b7-afb7-67f4d2b06b40

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
theorem _root_.solution {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulF a) := by
  have hof : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ)) :=
    continuous_id
  show Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x * a : Matrix (Fin n) (Fin n) ℂ))
  exact hof.matrix_mul continuous_const
end Formalism.FourierDecayAlt.P.B2x2
