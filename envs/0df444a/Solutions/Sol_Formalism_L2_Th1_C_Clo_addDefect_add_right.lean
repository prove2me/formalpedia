-- Prove2me | solution 1 for Formalism.L2.Th1.C.Clo.addDefect_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:40.530644+00:00
-- url     : https://prove2.me/submissions/fbd9f051-e34f-4766-91ee-7b822c38e910

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Pts_addDefect_comm


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
variable [CharZero K] {ph : PowerSeries K} {σ : Type}
namespace Formalism.L2.Th1.C.Clo
theorem _root_.solution (h1 : F1 R l linv ph) {x y y' : MvPowerSeries σ K} (hx : IsPt R x)
    (hy : IsPt R y) (hy' : IsPt R y') :
    LG R (be0 l linv ph x (fadd l linv y y') - (be0 l linv ph x y + be0 l linv ph x y')) := by
  have := h1 σ y y' x hy hy' hx
  rw [Pts.addDefect_comm ph _ x, Pts.addDefect_comm ph y x, Pts.addDefect_comm ph y' x] at this
  exact this
end Formalism.L2.Th1.C.Clo
