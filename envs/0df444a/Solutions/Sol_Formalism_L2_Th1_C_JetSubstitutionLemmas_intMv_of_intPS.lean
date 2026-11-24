-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.intMv_of_intPS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:29.428986+00:00
-- url     : https://prove2.me/submissions/f13be134-8634-45d2-8420-cfcf990ab80d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG

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
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K]
variable {R : Subring K}
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {f : PowerSeries K} (h : IntPS R f) : IntMv R (f : MvPowerSeries Unit K) := by
  intro n
  have hn : n = Finsupp.single () (n ()) := by
    ext ⟨⟩
    simp
  have := h (n ())
  rw [hn]
  exact this
end Formalism.L2.Th1.C.JetSubstitutionLemmas
