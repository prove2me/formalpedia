-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.dm_qminorRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:54.265802+00:00
-- url     : https://prove2.me/submissions/d2b12c1f-37e0-4bc1-a8fd-7933290740dd

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_intCast
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_ofFn_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_Tm_dualE
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_arg_rev
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_arg_rev
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_conjRev_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmStar_sign_conjRev


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
theorem _root_.solution {n t : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin t → Fin n) (w : ℂ) :
    (qminorRow E (b ∘ Fin.rev) (a ∘ Fin.rev) w).dualMap = qminor (dualE E) a b w := by
  unfold qminor qminorRow
  rw [dm_sum]
  refine Fintype.sum_equiv (PI.UnitaryGroupMassFormula.QmStar.conjRev t) _ _ (fun σ => ?_)
  rw [dm_mul, dm_intCast, dm_ofFn_prod, PI.UnitaryGroupMassFormula.QmStar.sign_conjRev, Int.cast_comm]
  simp only [Function.comp_apply, PI.UnitaryGroupMassFormula.QmStar.conjRev_apply, Fin.rev_rev, arg_rev, Tm_dualE]
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
