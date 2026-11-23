-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.endInt_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:07.667997+00:00
-- url     : https://prove2.me/submissions/78336d61-6717-4214-8c73-6c279feeffea

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_add
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_one
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Clo
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {R : Subring K} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Clo
theorem _root_.solution (h : IsLogPair l linv) (hF : FGInt R l linv) (n : ℕ) :
    EndInt R l linv (n : K) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact Pts.endInt_zero h
  | succ n ih => rw [Nat.cast_succ]; exact Pts.endInt_add h hF ih (Pts.endInt_one h)
end Formalism.L2.Th1.C.Clo
