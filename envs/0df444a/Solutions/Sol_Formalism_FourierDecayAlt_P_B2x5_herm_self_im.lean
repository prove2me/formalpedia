-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.herm_self_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:14.013272+00:00
-- url     : https://prove2.me/submissions/bce66be3-58ac-4af6-8ef0-d4a852125efc

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_Hherm

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
theorem _root_.solution (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) : (herm (Hpk k r) y y).im = 0 := by
  exact Complex.conj_eq_iff_im.mp (herm_conj _ (Hherm k r) y y)
end Formalism.FourierDecayAlt.P.B2x5
