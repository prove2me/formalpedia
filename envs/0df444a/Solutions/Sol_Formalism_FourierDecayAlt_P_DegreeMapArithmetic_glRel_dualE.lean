-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.glRel_dualE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:43:42.290819+00:00
-- url     : https://prove2.me/submissions/1aaa187b-a1e1-4370-a234-9ab5f5e7b949

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_zero

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) : GlRel (dualE E) := by
  intro a b c d
  simp only [dualE]
  rw [← dm_mul, ← dm_mul, ← dm_sub, hE d c b a, dm_sub]
  split_ifs <;> simp_all [dm_zero]
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
