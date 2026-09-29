-- Prove2me | solution 1 for FormalGroup.coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ab0793d5-244b-5418-9ba8-5634174b0b22

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_LawHom_subst_nthSeries_series_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (F₀ : FormalGroup k) (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (hsq : (maximalIdeal T) ^ 2 = ⊥)
    (resT : T →+* k) (hker : RingHom.ker resT = maximalIdeal T)
    (G G' : FormalGroup T) (hG : G.IsBaseChange resT F₀) (hG' : G'.IsBaseChange resT F₀)
    (ψ : FormalGroup.LawIso G G') (hψ : ∀ m : ℕ, resT (PowerSeries.coeff m ψ.series) = if m = 1 then 1 else 0) :
    PowerSeries.coeff q (G.nthSeries q) = PowerSeries.coeff q (G'.nthSeries q) := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  haveI : IsAdicComplete (⊥ : Ideal k) k := inferInstance
  obtain ⟨u₀, hu₀, hqF₀⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (⊥ : Ideal k) F₀ q).mp hF₀

  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hker, RingHom.mem_ker]
  have hmm : ∀ a b : T, a ∈ maximalIdeal T → b ∈ maximalIdeal T → a * b = 0 := by
    intro a b ha hb
    have : a * b ∈ maximalIdeal T ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rwa [hsq, Ideal.mem_bot] at this

  set A := G.nthSeries q with hA
  set B := G'.nthSeries q with hB
  set s := ψ.series with hs
  have hredA : PowerSeries.map resT A = u₀ * PowerSeries.X ^ (q * q) := by
    rw [hA, ← FormalGroup.IsBaseChange.nthSeries_eq_map G resT F₀ hG q, hqF₀]
  have hredB : PowerSeries.map resT B = u₀ * PowerSeries.X ^ (q * q) := by
    rw [hB, ← FormalGroup.IsBaseChange.nthSeries_eq_map G' resT F₀ hG' q, hqF₀]
  have hreds : PowerSeries.map resT s = PowerSeries.X := by
    ext m; rw [PowerSeries.coeff_map, hs, hψ m, PowerSeries.coeff_X]

  have hApow : ∀ (d j : ℕ), 1 ≤ d → j < q * q → PowerSeries.coeff j (A ^ d) ∈ maximalIdeal T := by
    intro d j hd hj
    rw [hmem, ← PowerSeries.coeff_map, map_pow, hredA, mul_pow, ← pow_mul, PowerSeries.coeff_mul_X_pow', if_neg]
    have : q * q ≤ q * q * d := Nat.le_mul_of_pos_right _ hd
    omega
  have hBj : ∀ j : ℕ, j < q * q → PowerSeries.coeff j B ∈ maximalIdeal T := by
    intro j hj
    rw [hmem, ← PowerSeries.coeff_map, hredB, PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
  have hqlt : q < q * q := by nlinarith

  have hscoef : ∀ m : ℕ, m ≠ 1 → PowerSeries.coeff m s ∈ maximalIdeal T := by
    intro m hm; rw [hmem, ← PowerSeries.coeff_map, hreds, PowerSeries.coeff_X, if_neg hm]
  have hs1 : PowerSeries.coeff 1 s - 1 ∈ maximalIdeal T := by
    rw [hmem, map_sub, ← PowerSeries.coeff_map, hreds, PowerSeries.coeff_X, if_pos rfl, map_one, sub_self]
  have hs0 : PowerSeries.constantCoeff s = 0 := ψ.constantCoeff_series
  have hsX : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero' hs0
  have hAX : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' (G.constantCoeff_nthSeries q)

  obtain ⟨w, hw⟩ := PowerSeries.X_dvd_iff.mpr hs0
  have hspow_gt : ∀ n : ℕ, q < n → PowerSeries.coeff q (s ^ n) = 0 := by
    intro n hn
    rw [hw, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hspow_red : ∀ n : ℕ, PowerSeries.coeff q (s ^ n) - (if n = q then 1 else 0) ∈ maximalIdeal T := by
    intro n
    rw [hmem, map_sub, ← PowerSeries.coeff_map, map_pow, hreds, PowerSeries.coeff_X_pow]
    by_cases h : n = q
    · subst h; rw [if_pos rfl, if_pos rfl, map_one, sub_self]
    · rw [if_neg (Ne.symm h), if_neg h, map_zero, sub_self]

  have hT2 := FormalGroup.LawHom.subst_nthSeries_series_eq ψ.toLawHom q
  rw [← hA, ← hB] at hT2
  change PowerSeries.subst A s = PowerSeries.subst s B at hT2

  have hL : PowerSeries.coeff q (PowerSeries.subst A s) = PowerSeries.coeff q A := by
    rw [PowerSeries.coeff_subst' hAX, finsum_eq_single _ 1]
    · rw [pow_one, smul_eq_mul]
      have : (PowerSeries.coeff 1 s - 1) * PowerSeries.coeff q A = 0 := hmm _ _ hs1 (by
        have := hApow 1 q le_rfl hqlt; rwa [pow_one] at this)
      calc PowerSeries.coeff 1 s * PowerSeries.coeff q A
          = (PowerSeries.coeff 1 s - 1) * PowerSeries.coeff q A + PowerSeries.coeff q A := by ring
        _ = PowerSeries.coeff q A := by rw [this, _root_.zero_add]
    · intro d hd
      rcases Nat.lt_or_gt_of_ne hd with hd0 | hd2
      · have : d = 0 := by omega
        subst this
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0, zero_smul]
      · rw [smul_eq_mul]
        exact hmm _ _ (hscoef d hd) (hApow d q (by omega) hqlt)

  have hR : PowerSeries.coeff q (PowerSeries.subst s B) = PowerSeries.coeff q B := by
    rw [PowerSeries.coeff_subst' hsX, finsum_eq_single _ q]
    · rw [smul_eq_mul]
      have : PowerSeries.coeff q B * (PowerSeries.coeff q (s ^ q) - 1) = 0 :=
        hmm _ _ (hBj q hqlt) (by simpa using hspow_red q)
      calc PowerSeries.coeff q B * PowerSeries.coeff q (s ^ q)
          = PowerSeries.coeff q B * (PowerSeries.coeff q (s ^ q) - 1) + PowerSeries.coeff q B := by ring
        _ = PowerSeries.coeff q B := by rw [this, _root_.zero_add]
    · intro n hn
      rw [smul_eq_mul]
      rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
      · exact hmm _ _ (hBj n (by omega)) (by simpa [if_neg hn] using hspow_red n)
      · rw [hspow_gt n hgt, mul_zero]
  rw [← hL, hT2, hR]

end S_FormalGroup_coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot
end P2MW
export P2MW.S_FormalGroup_coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot (solution)
