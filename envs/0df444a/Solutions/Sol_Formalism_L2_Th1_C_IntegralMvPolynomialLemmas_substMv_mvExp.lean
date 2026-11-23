-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:21.094188+00:00
-- url     : https://prove2.me/submissions/8b82d8c0-a054-4c7d-a319-644831cc20d1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
theorem _root_.solution {τ : Type} [Finite σ] {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := by
  unfold mvExp
  rw [subst_def, subst_def]
  exact MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero hf).const
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) (exp K)
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
