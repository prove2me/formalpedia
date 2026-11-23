-- Prove2me | solution 1 for Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:36.443471+00:00
-- url     : https://prove2.me/submissions/8e52d00e-576d-4c98-bc81-56fcdc54f949

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_degree_snd_lt
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_one

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
theorem _root_.solution {U V : MvPowerSeries σ K} (hU : IntMv R U)
    (hU0 : MvPowerSeries.constantCoeff U = 1) (hUV : U * V = 1) : IntMv R V := by
  classical
  have hV : V = 1 - (U - 1) * V := by rw [sub_mul, hUV]; ring
  have hh : IntMv R (U - 1) := fun n => by
    rw [map_sub]; exact R.sub_mem (hU n) (intMv_one n)
  have hh0 : MvPowerSeries.coeff 0 (U - 1) = 0 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, hU0, map_one, sub_self]
  have key : ∀ (m : ℕ) (n : σ →₀ ℕ), n.degree = m → MvPowerSeries.coeff n V ∈ R := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hn
      rw [hV, map_sub, MvPowerSeries.coeff_mul]
      refine R.sub_mem (intMv_one n) (Subring.sum_mem _ fun p hp => ?_)
      by_cases h1 : p.1 = 0
      · rw [h1, hh0, zero_mul]; exact R.zero_mem
      · exact R.mul_mem (hh _) (ih _ (hn ▸ degree_snd_lt hp h1) _ rfl)
  exact fun n => key _ n rfl
end Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
