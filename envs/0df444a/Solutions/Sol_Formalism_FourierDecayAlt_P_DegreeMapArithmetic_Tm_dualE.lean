-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.Tm_dualE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:10:45.477021+00:00
-- url     : https://prove2.me/submissions/fd854267-5adc-4a81-af66-263e8496f552

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_algebraMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DegreeMapArithmetic
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.DegreeMapArithmetic
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (u : ℂ) (a b : Fin n) :
    Tm (dualE E) u a b = (Tm E u b a).dualMap := by
  simp only [Tm, dualE, dm_add]
  congr 1
  by_cases h : a = b
  · subst h; simp [dm_algebraMap]
  · rw [if_neg h, if_neg (Ne.symm h), dm_zero]
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
