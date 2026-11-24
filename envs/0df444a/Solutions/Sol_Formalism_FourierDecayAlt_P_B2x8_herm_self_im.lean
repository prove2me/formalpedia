-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.herm_self_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:47.816392+00:00
-- url     : https://prove2.me/submissions/80ce5803-b9b3-48b0-a633-ee9cead902ac

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


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
theorem _root_.solution (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) : (herm (Hpk k r) y y).im = 0 := (Complex.conj_eq_iff_im).mp (herm_conj (Hpk k r) (Hpk_herm k r) y y)
end Formalism.FourierDecayAlt.P.B2x8
