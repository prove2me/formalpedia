-- Prove2me | solution 1 for Formalism.L2.Th1.C.Pts.intMv_of_intPS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:22:05.851315+00:00
-- url     : https://prove2.me/submissions/5aa813bc-32e7-4d74-8bc4-bd2bc5e14a1a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Pts
open IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Pts
theorem _root_.solution {f : PowerSeries K} (hf : IntPS R f) : IntMv R (f : MvPowerSeries Unit K) := by
  intro n
  have : n = Finsupp.single () (n ()) := by
    ext
    simp
  rw [this]
  exact hf (n ())
end Formalism.L2.Th1.C.Pts
