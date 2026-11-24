-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.subst_ph_linv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:52.248286+00:00
-- url     : https://prove2.me/submissions/4e789cc8-7022-4d08-b01d-9dbdaf483180

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
theorem _root_.solution {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K)
    {g : MvPowerSeries σ K} (hg : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (PowerSeries.subst g linv) ph =
      PowerSeries.subst g (PowerSeries.subst linv ph) := by
  exact (PowerSeries.subst_comp_subst_apply (hs1 h.2.2.1) (hsM hg) ph).symm
end Formalism.L2.Th1.C.JetSubstitutionLemmas
