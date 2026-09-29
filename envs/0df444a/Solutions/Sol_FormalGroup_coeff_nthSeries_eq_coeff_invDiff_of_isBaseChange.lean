-- Prove2me | solution 1 for FormalGroup.coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/46775e6f-5b82-5f91-99a2-83dcc55f5ad5

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_IsBaseChange_invDiff_eq_map
import Theorems.Thm_FormalGroup_subst_nthSeries_invDiff_mul_derivative
import Theorems.Thm_FormalGroup_coeff_one_nthSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange

set_option autoImplicit false

open FormalGroup

theorem solution
    (p : ℕ) [Fact p.Prime] {A R : Type*} [CommRing A] [CommRing R] [CharP R p]
    (hA : ∀ a : A, (p : A) * a = 0 → a = 0)
    (Fl : FormalGroup A) [Fl.IsComm] (f : A →+* R) (G : FormalGroup R) (hG : Fl.IsBaseChange f G) :
    PowerSeries.coeff p (G.nthSeries p) = PowerSeries.coeff (p - 1) G.invDiff := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos

  rw [FormalGroup.IsBaseChange.nthSeries_eq_map Fl f G hG p, FormalGroup.IsBaseChange.invDiff_eq_map Fl f G hG,
    PowerSeries.coeff_map, PowerSeries.coeff_map]
  set I : Ideal A := Ideal.span {(p : A)} with hI
  have hpI : (p : A) ∈ I := Ideal.mem_span_singleton_self _
  suffices key : PowerSeries.coeff p (Fl.nthSeries p) - PowerSeries.coeff (p - 1) Fl.invDiff ∈ I by
    rw [Ideal.mem_span_singleton] at key
    obtain ⟨a, ha⟩ := key
    have : f (PowerSeries.coeff p (Fl.nthSeries p) - PowerSeries.coeff (p - 1) Fl.invDiff) = 0 := by
      rw [ha, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
    rwa [map_sub, sub_eq_zero] at this

  set N : PowerSeries A := Fl.nthSeries p with hN
  set ω : PowerSeries A := Fl.invDiff with hω
  have hN0 : PowerSeries.constantCoeff N = 0 := Fl.constantCoeff_nthSeries p
  have hN1 : PowerSeries.coeff 1 N = p := by rw [hN, FormalGroup.coeff_one_nthSeries]
  have hω0 : PowerSeries.constantCoeff ω = 1 := Fl.constantCoeff_invDiff
  have hNs : PowerSeries.HasSubst N := PowerSeries.HasSubst.of_constantCoeff_zero' hN0

  set u : PowerSeries A := PowerSeries.subst N ω with hu
  have hu0 : PowerSeries.coeff 0 u = 1 := by
    rw [hu, PowerSeries.coeff_subst' hNs, finsum_eq_single _ 0]
    · rw [pow_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hω0, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_one, one_smul]
    · intro d hd
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hN0, zero_pow hd, smul_zero]
  have huu : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hu0]; exact isUnit_one
  obtain ⟨v, hv⟩ := huu.exists_right_inv
  have hcab : u * PowerSeries.derivative A N = PowerSeries.C (p : A) * ω := by
    rw [hu, hN, hω, FormalGroup.subst_nthSeries_invDiff_mul_derivative Fl p, nsmul_eq_mul, map_natCast]

  have hderI : ∀ k, PowerSeries.coeff k (PowerSeries.derivative A N) ∈ I := by
    intro k
    have e : PowerSeries.derivative A N = PowerSeries.C (p : A) * (ω * v) := by
      calc PowerSeries.derivative A N = (u * v) * PowerSeries.derivative A N := by rw [hv, one_mul]
        _ = v * (u * PowerSeries.derivative A N) := by ring
        _ = v * (PowerSeries.C (p : A) * ω) := by rw [hcab]
        _ = PowerSeries.C (p : A) * (ω * v) := by ring
    rw [e, PowerSeries.coeff_C_mul]
    exact I.mul_mem_right _ hpI
  have hkb : ∀ k : ℕ, PowerSeries.coeff (k + 1) N * ((k : A) + 1) ∈ I := by
    intro k; have := hderI k; rwa [PowerSeries.coeff_derivative] at this

  have hbI : ∀ k, 1 ≤ k → k < p → PowerSeries.coeff k N ∈ I := by
    intro k hk1 hkp
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hcop : IsCoprime ((k' + 1 : ℕ) : ℤ) (p : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => by
        have := Nat.le_of_dvd (by omega) h; omega))
    obtain ⟨a, b, hab⟩ := hcop
    have e' : (a : A) * ((k' : A) + 1) + (b : A) * (p : A) = 1 := by
      have := congrArg (Int.cast : ℤ → A) hab
      push_cast at this
      exact this
    have h1 := hkb k'
    have : PowerSeries.coeff (k' + 1) N =
        (a : A) * (PowerSeries.coeff (k' + 1) N * ((k' : A) + 1)) + (b : A) * PowerSeries.coeff (k' + 1) N * (p : A) := by
      linear_combination (-(PowerSeries.coeff (k' + 1) N)) * e'
    rw [this]
    exact I.add_mem (I.mul_mem_left _ h1) (I.mul_mem_left _ hpI)

  let π : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hπp : π (p : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  have hNbar : ∀ j, j < p → PowerSeries.coeff j (PowerSeries.map π N) = 0 := by
    intro j hj
    rw [PowerSeries.coeff_map]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hN0, map_zero]
    · by_cases hj1 : j = 1
      · subst hj1; rw [hN1, hπp]
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr (hbI j hj0 hj)
  obtain ⟨g, hg⟩ : ∃ g : PowerSeries (A ⧸ I), PowerSeries.map π N = PowerSeries.X ^ p * g := by
    refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (n + p) (PowerSeries.map π N), ?_⟩
    ext d
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with h
    · rw [PowerSeries.coeff_mk, Nat.sub_add_cancel h]
    · exact hNbar d (not_le.mp h)
  have hg0 : PowerSeries.constantCoeff (PowerSeries.X ^ p * g) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have huI : ∀ j, 1 ≤ j → j < p → PowerSeries.coeff j u ∈ I := by
    intro j hj1 hjp
    rw [← Ideal.Quotient.eq_zero_iff_mem, show Ideal.Quotient.mk I (PowerSeries.coeff j u) = π (PowerSeries.coeff j u) from rfl,
      ← PowerSeries.coeff_map, hu]
    have em : ∀ q : PowerSeries A, MvPowerSeries.map π q = PowerSeries.map π q := fun _ => rfl
    rw [show PowerSeries.map π (PowerSeries.subst N ω) = MvPowerSeries.map π (PowerSeries.subst N ω) from rfl,
      PowerSeries.map_subst hNs]
    try simp only [em]
    rw [hg, PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hg0)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega), smul_zero]
    · rw [mul_pow, ← pow_mul, PowerSeries.coeff_X_pow_mul', if_neg, smul_zero]
      have : p ≤ p * d := Nat.le_mul_of_pos_right _ hd
      omega

  have hcoef := congrArg (PowerSeries.coeff (p - 1)) hcab
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_C_mul,
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add (p - 1)) : ((0, p - 1) : ℕ × ℕ) ∈ _)] at hcoef
  have hrest : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (p - 1) \ {((0, p - 1) : ℕ × ℕ)},
      PowerSeries.coeff x.1 u * PowerSeries.coeff x.2 (PowerSeries.derivative A N) ∈ Ideal.span {(p : A) * p} := by
    refine Ideal.sum_mem _ fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx1
    have hx0 : 1 ≤ x.1 := by
      by_contra h0
      apply hx2
      rw [Finset.mem_singleton, Prod.ext_iff]
      refine ⟨?_, ?_⟩
      · show x.1 = 0
        omega
      · show x.2 = p - 1
        omega
    rw [← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_mem_mul (huI x.1 hx0 (by omega)) (hderI x.2)
  rw [Ideal.mem_span_singleton] at hrest
  obtain ⟨t, ht⟩ := hrest
  have hlead : PowerSeries.coeff (p - 1) (PowerSeries.derivative A N) = PowerSeries.coeff p N * (p : A) := by
    rw [PowerSeries.coeff_derivative, Nat.sub_add_cancel hp0, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hp.ne_zero),
      Nat.cast_one, sub_add_cancel]
  rw [hu0, one_mul, ht, hlead] at hcoef

  have hzero : (p : A) * (PowerSeries.coeff p N - PowerSeries.coeff (p - 1) ω + p * t) = 0 := by
    linear_combination hcoef
  have := hA _ hzero
  rw [show PowerSeries.coeff p N - PowerSeries.coeff (p - 1) ω = -((p : A) * t) by linear_combination this]
  exact I.neg_mem (I.mul_mem_right _ hpI)

end S_FormalGroup_coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange
end P2MW
export P2MW.S_FormalGroup_coeff_nthSeries_eq_coeff_invDiff_of_isBaseChange (solution)
