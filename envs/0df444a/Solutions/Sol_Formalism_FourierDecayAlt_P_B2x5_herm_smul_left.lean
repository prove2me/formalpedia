-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.herm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:47:28.203802+00:00
-- url     : https://prove2.me/submissions/164a7376-f2aa-46d8-8f5f-c5d7ed8cc38a

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
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (c : ℂ) (u v : ι → ℂ) : herm H (c • u) v = c * herm H u v := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]
end Formalism.FourierDecayAlt.P.B2x5
