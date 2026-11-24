-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.mat_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:44:33.027433+00:00
-- url     : https://prove2.me/submissions/6b664e75-238c-4186-9a6d-b0581ca2af57

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (h : ∀ u, A *ᵥ u = B *ᵥ u) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec, dotProduct, Pi.single_apply] using this
end Formalism.FourierDecayAlt.P.B2x5
