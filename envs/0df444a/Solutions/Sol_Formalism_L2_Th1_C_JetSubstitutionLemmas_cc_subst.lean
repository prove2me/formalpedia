-- Prove2me | solution 1 for Formalism.L2.Th1.C.JetSubstitutionLemmas.cc_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:49.368973+00:00
-- url     : https://prove2.me/submissions/e1b519d3-916d-4618-af9e-b55abf3f68f9

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
namespace Formalism.L2.Th1.C.JetSubstitutionLemmas
theorem _root_.solution {σ : Type} {a : MvPowerSeries σ K} (ha : MvPowerSeries.constantCoeff a = 0)
    (g : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a g) = PowerSeries.constantCoeff g := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  simp only [map_pow, ha]
  rw [finsum_eq_single _ 0 (fun d hd => by simp [zero_pow hd])]
  simp
end Formalism.L2.Th1.C.JetSubstitutionLemmas
