-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.measurable_herm_im_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:06:01.197043+00:00
-- url     : https://prove2.me/submissions/c626e19d-6980-448c-ab6c-056b52b0c0f4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_herm

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
theorem _root_.solution (k r : ℕ) (y₀ : Fin (2 * r + k + 1) → ℂ) :
    Measurable fun y : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) y y₀).im := (Complex.continuous_im.comp ((continuous_herm _).comp (continuous_id.prodMk continuous_const))).measurable
end Formalism.FourierDecayAlt.P.B2x5
