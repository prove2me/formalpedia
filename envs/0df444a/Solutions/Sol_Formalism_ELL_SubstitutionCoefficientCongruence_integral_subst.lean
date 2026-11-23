-- Prove2me | solution 1 for Formalism.ELL.SubstitutionCoefficientCongruence.integral_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:34.426519+00:00
-- url     : https://prove2.me/submissions/ecb6d7af-2a96-413a-ba5b-d6ec44f6387d

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_mem_unitBall
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
namespace Formalism.ELL.SubstitutionCoefficientCongruence
section Chain
variable {R : Type*} [CommRing R] {σ : Type*}
private theorem coeff_subst_congr_lemma {R : Type*} [CommRing R] {σ : Type*}
    {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0) (n : ℕ) :
    ∀ e : σ →₀ ℕ, e.degree < n → MvPowerSeries.coeff e (a ^ n) = 0 := by
  classical
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_lt_zero _)
  | succ n ih =>
    intro e he
    rw [pow_succ, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h2 : x.2 = 0
    · have h0 : MvPowerSeries.coeff 0 a = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha]
      rw [h2, h0, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).1 h)
      have hsum : x.1.degree + x.2.degree = e.degree := by rw [← map_add, hx]
      have h1 : x.1.degree < n := by omega
      rw [ih x.1 h1, zero_mul]
end Chain
section Integral
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}
end Integral
end Formalism.ELL.SubstitutionCoefficientCongruence
namespace Formalism.ELL
end Formalism.ELL
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.SubstitutionCoefficientCongruence
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}
namespace Formalism.ELL.SubstitutionCoefficientCongruence
theorem _root_.solution {c : PowerSeries K} (hc : ∀ n, ‖coeff n c‖ ≤ 1)
    {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : Formalism.G.IntegralMv f) : Formalism.G.IntegralMv (c.subst f) := by
  classical
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf0
  intro e
  rw [← mem_unitBall, PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (e.degree + 1)) ?_]
  · exact Subring.sum_mem _ fun d _ => by
      rw [smul_eq_mul]
      exact Subring.mul_mem _ (mem_unitBall.2 (hc d)) (mem_unitBall.2 (integral_pow hf d e))
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [coeff_subst_congr_lemma hf0 d e (by omega), smul_zero])
end Formalism.ELL.SubstitutionCoefficientCongruence
