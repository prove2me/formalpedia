-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.comm_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:11:05.074548+00:00
-- url     : https://prove2.me/submissions/6a96df1c-70e3-499e-b6f4-a24f03ed47c7

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_comm_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_DegreeMapArithmetic_comm_pow

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
theorem _root_.solution (H : Module.End ℂ V) {n : ℕ} (f : Fin n → Module.End ℂ V) (d : Fin n → ℂ)
    (h : ∀ x, H * f x = f x * H + d x • f x) (a : Fin n → ℕ) :
    H * mono f a = mono f a * H + (∑ x, (a x : ℂ) * d x) • mono f a := by
  unfold mono
  exact comm_prod H (fun x => f x ^ a x) (fun x => (a x : ℂ) * d x) (fun x => comm_pow H (f x) (d x) (h x) (a x))
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
