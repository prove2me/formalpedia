-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.measurable_herm_im_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:03:03.54352+00:00
-- url     : https://prove2.me/submissions/01d2c625-a953-4bd5-ae42-418dbc6f028f

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
    Measurable fun y : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) y₀ y).im := (Complex.continuous_im.comp ((continuous_herm _).comp (continuous_const.prodMk continuous_id))).measurable
end Formalism.FourierDecayAlt.P.B2x5
