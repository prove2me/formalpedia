-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_substMv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:27.733078+00:00
-- url     : https://prove2.me/submissions/6a2f087b-a3a9-4d44-8b35-89b374d47197

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_pow
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_prod

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
variable {K : Type} [Field K] {σ : Type} {R : Subring K}
namespace Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
theorem _root_.solution {τ : Type} [Finite σ] {F : MvPowerSeries σ K} (hF : IntMv R F)
    {a : σ → MvPowerSeries τ K} (ha : ∀ s, IsPt R (a s)) : IntMv R (MvPowerSeries.subst a F) := by
  intro e
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => (ha s).1)]
  refine finsum_induction (· ∈ R) R.zero_mem (fun _ _ => R.add_mem) fun d => ?_
  rw [smul_eq_mul]
  exact R.mul_mem (hF d) (intMv_prod _ (fun s _ => intMv_pow (ha s).2 _) e)
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
