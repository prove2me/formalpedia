-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_lev_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:52:13.429672+00:00
-- url     : https://prove2.me/submissions/4e424bf0-5623-48a3-9fd0-95eb86a119de

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_lev_one

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {g : Mat k r'} (hg : IsUnit g.det) : (ιLev k 1 r' g)⁻¹ = ιLev k 1 r' g⁻¹ := by
  exact Matrix.inv_eq_right_inv (by rw [← al_lev_mul, Matrix.mul_nonsing_inv _ hg, al_lev_one])
end Formalism.FourierDecayAlt.P.B2x8
