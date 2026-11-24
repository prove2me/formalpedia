-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.cc_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:22:09.124235+00:00
-- url     : https://prove2.me/submissions/6743eb21-0cfd-4c43-8754-87a5892f8309

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_subst1

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
open JetSubstitutionLemmas
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (a : K) :
    PowerSeries.constantCoeff (mulBy l linv a) = 0 := by
  unfold mulBy
  rw [cc_subst1 (by simp [h.1]) linv]
  exact h.2.2.1
end Formalism.L2.Th1.C.JetSubstitutionLemmas
