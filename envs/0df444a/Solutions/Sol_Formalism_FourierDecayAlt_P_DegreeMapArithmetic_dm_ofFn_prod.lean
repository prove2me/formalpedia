-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.dm_ofFn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:43:40.420042+00:00
-- url     : https://prove2.me/submissions/2acb38b8-9809-4758-aacc-a885d8e6f9ca

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_dm_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
theorem _root_.solution : ∀ {t : ℕ} (f : Fin t → Module.End ℂ V),
    ((List.ofFn f).prod).dualMap = (List.ofFn fun i => (f i.rev).dualMap).prod
  | 0, f => by simp [dm_one]
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, dm_mul, solution (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => (f i.rev).dualMap), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
