-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.ut_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:15:28.889795+00:00
-- url     : https://prove2.me/submissions/6fb076f9-98bc-4794-93d4-8d49a4eb98b3

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_bt
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
theorem _root_.solution {u v : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (hv : v ∈ C2.UTset m) :
    u * v ∈ C2.UTset m :=
  ⟨fun i j h => ((ut_bt hu).mul (ut_bt hv)) h,
   fun i => by rw [bt_mul_diag Function.injective_id (ut_bt hu) (ut_bt hv), hu.2, hv.2, one_mul]⟩
end Formalism.FourierDecayAlt.P.C2x2
