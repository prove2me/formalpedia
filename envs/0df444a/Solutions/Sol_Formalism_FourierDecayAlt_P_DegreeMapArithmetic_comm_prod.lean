-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.comm_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:17:40.431388+00:00
-- url     : https://prove2.me/submissions/516acdc9-b7ea-4f50-aa3b-2348e0ef1b9a

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
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
theorem _root_.solution (H : Module.End ℂ V) : ∀ {n : ℕ} (g : Fin n → Module.End ℂ V) (e : Fin n → ℂ),
    (∀ x, H * g x = g x * H + e x • g x) →
    H * (List.ofFn g).prod = (List.ofFn g).prod * H + (∑ x, e x) • (List.ofFn g).prod
  | 0, g, e, _ => by simp
  | n + 1, g, e, h => by
    have ih := solution H (fun x => g x.succ) (fun x => e x.succ) (fun x => h x.succ)
    rw [List.ofFn_succ, List.prod_cons, ← mul_assoc, h 0, add_mul, mul_assoc, ih, Fin.sum_univ_succ, mul_add,
      add_smul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
