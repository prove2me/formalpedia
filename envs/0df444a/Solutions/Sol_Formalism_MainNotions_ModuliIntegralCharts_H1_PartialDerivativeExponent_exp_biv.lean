-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.exp_biv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:51:06.401301+00:00
-- url     : https://prove2.me/submissions/1a737ecd-e117-4642-b0a4-43c8c97f9f91

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
open MvPowerSeries
variable {σ : Type}
variable {k : Type} [CommRing k]
variable [Algebra ℚ k]
private lemma coeff_XX_pow_lemma (d : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X 0 + X 1 : MvPowerSeries (Fin 2) k) ^ d) =
      if e 0 + e 1 = d then ((d.choose (e 0) : ℕ) : k) else 0 := by
  rw [add_pow, map_sum]
  have key : ∀ m ∈ Finset.range (d + 1),
      coeff e ((X 0 : MvPowerSeries (Fin 2) k) ^ m * X 1 ^ (d - m) * (d.choose m : MvPowerSeries (Fin 2) k)) =
        if e 0 = m ∧ e 1 = d - m then (d.choose m : k) else 0 := by
    intro m _
    rw [← map_natCast (C : k →+* MvPowerSeries (Fin 2) k), coeff_mul_C, X_pow_eq, X_pow_eq,
      monomial_mul_monomial, coeff_monomial]
    have hiff : (e = Finsupp.single 0 m + Finsupp.single 1 (d - m)) ↔ (e 0 = m ∧ e 1 = d - m) := by
      constructor
      · rintro rfl
        simp
      · rintro ⟨h0, h1⟩
        ext i
        fin_cases i <;> simp [h0, h1]
    by_cases h : e 0 = m ∧ e 1 = d - m
    · rw [if_pos (hiff.2 h), if_pos h]
      simp
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, zero_mul]
  rw [Finset.sum_congr rfl key]
  by_cases hd : e 0 + e 1 = d
  · rw [if_pos hd, Finset.sum_eq_single (e 0)]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro m _ hm
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hm h.symm
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    rw [if_neg]
    rintro ⟨h0, h1⟩
    omega
private lemma coeff_substX_lemma_2 (i : Fin 2) (f : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    coeff e (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) f) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) f else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  simp_rw [coeff_X_pow]
  by_cases h : e = Finsupp.single i (e i)
  · rw [if_pos h, finsum_eq_single _ (e i)]
    · rw [if_pos h, smul_eq_mul, mul_one]
    · intro d hd
      rw [if_neg, smul_zero]
      intro h'
      apply hd
      rw [h']
      simp
  · rw [if_neg h]
    have hz : ∀ d : ℕ, (PowerSeries.coeff d f • if e = Finsupp.single i d then (1 : k) else 0) = 0 := by
      intro d
      rw [if_neg, smul_zero]
      intro h'
      apply h
      rw [h']
      simp
    simp only [hz, finsum_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
open MvPowerSeries
variable {σ : Type}
variable {k : Type} [CommRing k]
variable [Algebra ℚ k]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
theorem _root_.solution :
    PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) =
      PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by
  ext e
  have hsum : PowerSeries.HasSubst (X 0 + X 1 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hL : coeff e (PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0 + e 1) (PowerSeries.exp k) * ((e 0 + e 1).choose (e 0) : k) := by
    rw [PowerSeries.coeff_subst hsum, finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_XX_pow_lemma, if_pos rfl, smul_eq_mul]
    · intro d hd
      rw [coeff_XX_pow_lemma, if_neg (fun h => hd h.symm), smul_zero]
  have hR : coeff e (PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0) (PowerSeries.exp k) * PowerSeries.coeff (e 1) (PowerSeries.exp k) := by
    rw [coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
    · rw [coeff_substX_lemma_2, coeff_substX_lemma_2, if_pos (by simp), if_pos (by simp)]
      simp
    · rintro ⟨p, q⟩ hpq hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
      rw [coeff_substX_lemma_2, coeff_substX_lemma_2]
      by_cases h1 : p = Finsupp.single 0 (p 0)
      · by_cases h2 : q = Finsupp.single 1 (q 1)
        · exfalso
          apply hne
          have hq0 : q 0 = 0 := by
            rw [h2]
            simp
          have hp1 : p 1 = 0 := by
            rw [h1]
            simp
          have c0 := DFunLike.congr_fun hpq 0
          have c1 := DFunLike.congr_fun hpq 1
          simp only [Finsupp.coe_add, Pi.add_apply] at c0 c1
          rw [Prod.mk.injEq]
          constructor
          · rw [h1]
            congr 1
            omega
          · rw [h2]
            congr 1
            omega
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro h
      exfalso
      apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      ext i
      fin_cases i <;> simp
  rw [hL, hR, PowerSeries.coeff_exp, PowerSeries.coeff_exp, PowerSeries.coeff_exp,
    ← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]
  congr 1
  have hle : e 0 ≤ e 0 + e 1 := Nat.le_add_right _ _
  have h := Nat.choose_mul_factorial_mul_factorial hle
  rw [Nat.add_sub_cancel_left] at h
  have h' : ((e 0 + e 1).choose (e 0) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) =
      ((e 0 + e 1).factorial : ℚ) := by
    exact_mod_cast h
  have hc : ((e 0 + e 1).choose (e 0) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hle).ne'
  have hf0 : ((e 0).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hf1 : ((e 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  rw [← h']
  field_simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
