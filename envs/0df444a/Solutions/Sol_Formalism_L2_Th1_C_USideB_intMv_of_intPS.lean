-- Prove2me | solution 1 for Formalism.L2.Th1.C.USideB.intMv_of_intPS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:33.472112+00:00
-- url     : https://prove2.me/submissions/6a95057f-0107-4965-a7e9-c06e2de8ea8f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideB

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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open USideB
open Formalism.L2.Th1.C.USideB
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.USideB
theorem _root_.solution {R : Subring K} {f : PowerSeries K} (h : IntPS R f) :
    IntMv R (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun x => by cases x; simp
  rw [e]
  exact h (n ())
end Formalism.L2.Th1.C.USideB
