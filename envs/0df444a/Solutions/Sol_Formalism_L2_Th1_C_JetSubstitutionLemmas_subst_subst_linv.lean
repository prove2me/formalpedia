-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.subst_subst_linv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:56.919822+00:00
-- url     : https://prove2.me/submissions/1252d81d-3655-4349-8188-fd7ad4c0fa40

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hs1
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_hsM

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
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (PowerSeries.subst g linv) l = g := by
  rw [← PowerSeries.subst_comp_subst_apply (hs1 h.2.2.1) (hsM hg), h.2.2.2.2, PowerSeries.subst_X (hsM hg)]
end Formalism.L2.Th1.C.JetSubstitutionLemmas
