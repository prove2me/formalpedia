-- Prove2me | solution 1 for Formalism.ELL.SubstitutionCoefficientCongruence.coeff_subst_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:10.862859+00:00
-- url     : https://prove2.me/submissions/c688ca99-dc75-40b7-8879-ff39d6776a2c

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
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
variable {R : Type*} [CommRing R] {σ : Type*}
namespace Formalism.ELL.SubstitutionCoefficientCongruence
theorem _root_.solution {g h : PowerSeries R} {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (e : σ →₀ ℕ)
    (hgh : ∀ k ≤ e.degree, coeff k g = coeff k h) :
    MvPowerSeries.coeff e (g.subst a) = MvPowerSeries.coeff e (h.subst a) := by
  classical
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k ≤ e.degree
  · rw [hgh k hk]
  · rw [coeff_subst_congr_lemma ha k e (by omega), smul_zero, smul_zero]
end Formalism.ELL.SubstitutionCoefficientCongruence
