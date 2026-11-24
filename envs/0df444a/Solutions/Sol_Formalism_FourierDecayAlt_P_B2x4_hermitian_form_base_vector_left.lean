-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.hermitian_form_base_vector_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:44:04.40458+00:00
-- url     : https://prove2.me/submissions/63fecc05-f0fd-4407-a14c-c632ac744b6e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_Hpk_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_hermitian_first_basis_right
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution (k r' : ℕ) (w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (e0 k r') w = star (w (lastI k r')) := by
  rw [← herm_symm _ (Hpk_herm k (1 + r')), hermitian_first_basis_right]
end Formalism.FourierDecayAlt.P.B2x4
