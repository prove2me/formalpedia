-- Prove2me | solution 1 for Formalism.MainNotions.J.Ex_biv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:19.391874+00:00
-- url     : https://prove2.me/submissions/5de37751-e28d-4528-9af9-59f447c6ff33

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.J
open MvPowerSeries
section AlgebraTools
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]
private theorem powerSeries_hasSubst_of_constantCoeff_eq_zero {τ : Type} {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) :
    PowerSeries.HasSubst f := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hf
  | (show IsNilpotent _; rw [hf]; exact IsNilpotent.zero)
private theorem coeff_diagS [DecidableEq ι] (a : PowerSeries R) (i : ι) (e : ι →₀ ℕ) :
    coeff e (diagS a i : MvPowerSeries ι R) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) a else 0 := by
  have hX : PowerSeries.HasSubst (X i : MvPowerSeries ι R) := powerSeries_hasSubst_of_constantCoeff_eq_zero (constantCoeff_X i)
  unfold diagS
  rw [PowerSeries.coeff_subst hX]
  have hterm : ∀ d : ℕ, PowerSeries.coeff d a • coeff e ((X i : MvPowerSeries ι R) ^ d) =
      if e = Finsupp.single i d then PowerSeries.coeff d a else 0 := by
    intro d
    first
    | (rw [MvPowerSeries.coeff_X_pow, smul_eq_mul]; split_ifs <;> simp)
    | (rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul]; split_ifs <;> simp)
  simp_rw [hterm]
  rw [finsum_eq_single _ (e i)]
  intro d hd
  have hne : ¬ e = Finsupp.single i d := fun he => hd (by rw [he, Finsupp.single_eq_same])
  simp [hne]
end AlgebraTools
section Exp
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
private theorem coeff_X_zero_add_X_one_pow (n : Fin 2 →₀ ℕ) (k : ℕ) :
    coeff n ((X 0 + X 1 : MvPowerSeries (Fin 2) K) ^ k) =
      if k = n 0 + n 1 then ((k.choose (n 0) : ℕ) : K) else 0 := by
  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      coeff n ((X 0 : MvPowerSeries (Fin 2) K) ^ m * X 1 ^ (k - m) *
        ((k.choose m : ℕ) : MvPowerSeries (Fin 2) K)) =
        if n = Finsupp.single 0 m + Finsupp.single 1 (k - m) then ((k.choose m : ℕ) : K) else 0 := by
    intro m _
    first
    | (rw [← nsmul_eq_mul', map_nsmul, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial, one_mul, MvPowerSeries.coeff_monomial, nsmul_eq_mul]
       split_ifs <;> simp)
    | (rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul,
        ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)), MvPowerSeries.coeff_mul_C,
        MvPowerSeries.coeff_monomial]
       split_ifs <;> simp)
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hk
  · rw [Finset.sum_eq_single (n 0)]
    · rw [if_pos]
      ext i
      fin_cases i <;> simp [hk]
    · intro m _ hm
      rw [if_neg]
      intro h
      apply hm
      have h0 := congrArg (fun e => e 0) h
      simp at h0
      omega
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro h
    apply hk
    have h0 := congrArg (fun e => e 0) h
    have h1 := congrArg (fun e => e 1) h
    simp at h0 h1
    rw [Finset.mem_range] at hm
    omega
end Exp
section Int
variable {ι κ : Type} {K : Type} [Field K]
end Int
end Formalism.MainNotions.J
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
namespace Formalism.MainNotions.J
theorem _root_.solution : Ex (X 0 + X 1 : MvPowerSeries (Fin 2) K) = Ex (X 0) * Ex (X 1) := by
  ext n
  have hs : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hL : coeff n (Ex (X 0 + X 1 : MvPowerSeries (Fin 2) K)) =
      PowerSeries.coeff (n 0 + n 1) (PowerSeries.exp K) * (((n 0 + n 1).choose (n 0) : ℕ) : K) := by
    unfold Ex
    rw [PowerSeries.coeff_subst (powerSeries_hasSubst_of_constantCoeff_eq_zero hs)]
    simp_rw [coeff_X_zero_add_X_one_pow]
    rw [finsum_eq_single _ (n 0 + n 1)]
    · simp
    · intro d hd
      simp [hd]
  have hR : coeff n (Ex (X 0 : MvPowerSeries (Fin 2) K) * Ex (X 1)) =
      PowerSeries.coeff (n 0) (PowerSeries.exp K) * PowerSeries.coeff (n 1) (PowerSeries.exp K) := by
    change coeff n (diagS (PowerSeries.exp K) 0 * diagS (PowerSeries.exp K) 1) = _
    rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (n 0), Finsupp.single 1 (n 1))]
    · rw [coeff_diagS, coeff_diagS]
      simp
    · intro p hp hne
      replace hp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [coeff_diagS, coeff_diagS]
      by_cases h1 : p.1 = Finsupp.single 0 (p.1 0)
      · by_cases h2 : p.2 = Finsupp.single 1 (p.2 1)
        · exfalso
          apply hne
          have e0 := congrArg (fun e => e 0) hp
          have e1 := congrArg (fun e => e 1) hp
          rw [h2] at e0
          rw [h1] at e1
          simp at e0 e1
          exact Prod.ext (h1.trans (congrArg (Finsupp.single 0) e0))
            (h2.trans (congrArg (Finsupp.single 1) e1))
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro h
      exfalso
      apply h
      refine Finset.HasAntidiagonal.mem_antidiagonal.mpr ?_
      ext i
      fin_cases i <;> simp
  rw [hL, hR]
  simp only [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast]
  rw [Nat.cast_add_choose]
  have hne : ((n 0 + n 1).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  first
  | (rw [div_mul_div_comm, one_mul, div_mul_cancel_left₀ hne]; simp)
  | (field_simp; done)
  | (field_simp; rw [mul_inv_cancel₀ hne, one_mul])
  | (field_simp; simp [hne])
  all_goals first | ring | exact mul_comm _ _
end Formalism.MainNotions.J
