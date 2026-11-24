-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.heis_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:01:31.238491+00:00
-- url     : https://prove2.me/submissions/9822fb02-eaf1-4ff4-bc6d-4b007fc5de46

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_sub_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_sub_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_symm

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
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution (hH : Hᴴ = H) (e v : Fin m → ℂ) (b : ℂ) (hee : herm H e e = 0) (hve : herm H v e = 0)
    (hb : b + star b + herm H v v = 0) (u w : Fin m → ℂ) :
    herm H (u - herm H u v • e + herm H u e • (v + b • e)) (w - herm H w v • e + herm H w e • (v + b • e)) =
      herm H u w := by
  have hev : herm H e v = 0 := by rw [← herm_symm H hH v e, hve, star_zero]
  simp only [herm_add_left, herm_sub_left, herm_smul_left, herm_add_right, herm_sub_right, herm_smul_right,
    herm_symm H hH, hee, hve, hev]
  linear_combination (herm H u e * herm H e w) * hb
end Formalism.FourierDecayAlt.P.B2x4
