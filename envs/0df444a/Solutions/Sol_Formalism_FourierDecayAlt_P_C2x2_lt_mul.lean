-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.lt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:24:25.440068+00:00
-- url     : https://prove2.me/submissions/24364d35-d765-42f8-8856-aea278e78e8a

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_lt_bt
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_bt_mul_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x2
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x2
theorem _root_.solution {u v : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.LTset m) (hv : v ∈ C2.LTset m) :
    u * v ∈ C2.LTset m :=
  ⟨fun i j h => ((lt_bt hu).mul (lt_bt hv)) (OrderDual.toDual_lt_toDual.mpr h),
   fun i => by rw [bt_mul_diag OrderDual.toDual.injective (lt_bt hu) (lt_bt hv), hu.2, hv.2, one_mul]⟩
end Formalism.FourierDecayAlt.P.C2x2
