-- Prove2me | solution 1 for FormalGroup.exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/961861bf-479c-5cbe-9ce5-b22c9ae478e5

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_LawHom_subst_nthSeries_series_eq
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_exists_nthSeries_eq_qfold_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso

set_option autoImplicit false

universe u

p2m_open "FormalGroup P2MW.S_FormalGroup_exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso.FormalGroup"

namespace FormalGroup
p2m_export "FormalGroup" "IsComm.comm IsComm 𝔾ₘ mk map nthSeries constantCoeff_nthSeries LawHom LawIso IsBaseChange LawHom.subst_nthSeries_series_eq IsDrinfeldBasisAdic IsBaseChange.nthSeries_eq_map exists_nthSeries_eq_qfold_of_isUnit"
namespace HasseCoeffTransportAux
p2m_open "FormalGroup"

section PS

variable {S : Type*} [CommRing S]

theorem constantCoeff_subst_of_constantCoeff_eq_zero (a f : PowerSeries S)
    (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  have e := PowerSeries.eq_X_mul_shift_add_const f
  conv_lhs => rw [e]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, PowerSeries.subst_C]
  show PowerSeries.constantCoeff (a * _ + PowerSeries.C (PowerSeries.constantCoeff f)) = _
  rw [map_add, map_mul, ha, zero_mul, _root_.zero_add, PowerSeries.constantCoeff_C]

theorem coeff_subst_of_X_pow_mul (φ g : PowerSeries S) (hφ : PowerSeries.constantCoeff φ = 0) (q : ℕ) (hq : 1 ≤ q) :
    PowerSeries.coeff q (PowerSeries.subst (PowerSeries.X ^ q * g) φ) =
      PowerSeries.coeff 1 φ * PowerSeries.constantCoeff g := by
  obtain ⟨χ, hχ⟩ := PowerSeries.X_dvd_iff.mpr hφ
  have hA0 : PowerSeries.constantCoeff (PowerSeries.X ^ q * g) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), zero_mul]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have h1 : PowerSeries.coeff 1 φ = PowerSeries.constantCoeff χ := by
    rw [hχ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.coeff_succ_X_mul 0 χ
  rw [h1, hχ, PowerSeries.subst_mul hs, PowerSeries.subst_X hs]
  show PowerSeries.coeff q (PowerSeries.X ^ q * g * PowerSeries.subst (PowerSeries.X ^ q * g) χ) = _
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, constantCoeff_subst_of_constantCoeff_eq_zero _ _ hA0, mul_comm]

theorem coeff_subst_X_pow_mul (φ g : PowerSeries S) (hφ : PowerSeries.constantCoeff φ = 0) (q : ℕ) :
    PowerSeries.coeff q (PowerSeries.subst φ (PowerSeries.X ^ q * g)) =
      PowerSeries.coeff 1 φ ^ q * PowerSeries.constantCoeff g := by
  obtain ⟨χ, hχ⟩ := PowerSeries.X_dvd_iff.mpr hφ
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hφ
  have h1 : PowerSeries.coeff 1 φ = PowerSeries.constantCoeff χ := by
    rw [hχ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.coeff_succ_X_mul 0 χ
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs, h1]
  show PowerSeries.coeff q (φ ^ q * PowerSeries.subst φ g) = _
  rw [hχ, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, ← hχ,
    constantCoeff_subst_of_constantCoeff_eq_zero _ _ hφ]

end PS

section Maps

variable {R S : Type*} [CommRing R] [CommRing S]

theorem isComm_map (F : FormalGroup R) [F.IsComm] (f : R →+* S) : (F.map f).IsComm where
  comm := by
    have hc : (F : MvPowerSeries (Fin 2) R) =
        (F : MvPowerSeries (Fin 2) R).subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] :=
      FormalGroup.IsComm.comm
    have hvec : (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) S) =
        fun i => ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) i).map f := by
      ext1 i; fin_cases i <;> simp
    show ((F : MvPowerSeries (Fin 2) R).map f) =
      ((F : MvPowerSeries (Fin 2) R).map f).subst ![MvPowerSeries.X 1, MvPowerSeries.X 0]
    rw [hvec, ← MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X, ← hc]

theorem isUnit_natCast_quot (q : ℕ) (hq : q.Prime) (k : ℕ) (hk : ¬ q ∣ k) :
    IsUnit ((k : ℕ) : R ⧸ Ideal.span {(q : R)}) := by
  have hcop : IsCoprime (k : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hk))
  obtain ⟨a, b, hab⟩ := hcop
  have hqz : ((q : ℕ) : R ⧸ Ideal.span {(q : R)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(q : R)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have := congrArg (Int.cast : ℤ → R ⧸ Ideal.span {(q : R)}) hab
  push_cast at this
  rw [hqz, mul_zero, _root_.add_zero] at this
  exact isUnit_iff_exists_inv'.mpr ⟨_, this⟩

theorem exists_map_nthSeries_eq_X_pow_mul (q : ℕ) [Fact q.Prime] (F : FormalGroup R) [F.IsComm] :
    ∃ g : PowerSeries (R ⧸ Ideal.span {(q : R)}),
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(q : R)})) (F.nthSeries q) = PowerSeries.X ^ q * g := by
  have hqp : q.Prime := Fact.out
  haveI := isComm_map F (Ideal.Quotient.mk (Ideal.span {(q : R)}))
  obtain ⟨h, g, hg⟩ := FormalGroup.exists_nthSeries_eq_qfold_of_isUnit
    (F.map (Ideal.Quotient.mk (Ideal.span {(q : R)}))) hqp.two_le
    (fun k _ hk => isUnit_natCast_quot q hqp k hk)
  have hqz : ((q : ℕ) : R ⧸ Ideal.span {(q : R)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(q : R)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  refine ⟨g, ?_⟩
  rw [← FormalGroup.IsBaseChange.nthSeries_eq_map F _ (F.map _) rfl q, hg, hqz, zero_smul, _root_.add_zero,
    ← Nat.cast_smul_eq_nsmul (R ⧸ Ideal.span {(q : R)}), hqz, zero_smul, _root_.zero_add]

end Maps

end FormalGroup.HasseCoeffTransportAux

open FormalGroup.HasseCoeffTransportAux

theorem solution
    {R : Type u} [CommRing R] (q : ℕ) [Fact q.Prime]
    (F F' : FormalGroup R) [F.IsComm] [F'.IsComm] (ψ : FormalGroup.LawIso F' F) :
    ∃ w : R, IsUnit w ∧
      PowerSeries.coeff q (F.nthSeries q) - w * PowerSeries.coeff q (F'.nthSeries q) ∈ Ideal.span {(q : R)} := by
  classical
  have hqp : q.Prime := Fact.out
  obtain ⟨uU, huU⟩ := ψ.isUnit_coeff_one
  refine ⟨(↑(uU * (uU⁻¹) ^ q) : R), Units.isUnit _, ?_⟩

  obtain ⟨g, hg⟩ := exists_map_nthSeries_eq_X_pow_mul q F
  obtain ⟨g', hg'⟩ := exists_map_nthSeries_eq_X_pow_mul q F'
  set π := Ideal.Quotient.mk (Ideal.span {(q : R)}) with hπ

  have hψ0 : PowerSeries.constantCoeff ψ.series = 0 := ψ.constantCoeff_series
  have hA'0 : PowerSeries.constantCoeff (F'.nthSeries q) = 0 := FormalGroup.constantCoeff_nthSeries F' q
  have hE := FormalGroup.LawHom.subst_nthSeries_series_eq ψ.toLawHom q
  have hES : PowerSeries.subst (PowerSeries.map π (F'.nthSeries q)) (PowerSeries.map π ψ.series) =
      PowerSeries.subst (PowerSeries.map π ψ.series) (PowerSeries.map π (F.nthSeries q)) := by
    have h1 := congrArg (MvPowerSeries.map π) hE
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hA'0),
      PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hψ0)] at h1
    exact h1
  rw [hg, hg'] at hES

  set φ := PowerSeries.map π ψ.series with hφ
  have hφ0 : PowerSeries.constantCoeff φ = 0 := by
    rw [hφ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hψ0, map_zero]
  have hφ1 : PowerSeries.coeff 1 φ = π ↑uU := by
    rw [hφ, PowerSeries.coeff_map, huU]
  have key : π ↑uU * PowerSeries.constantCoeff g' = π ↑uU ^ q * PowerSeries.constantCoeff g := by
    rw [← hφ1, ← coeff_subst_of_X_pow_mul φ g' hφ0 q hqp.one_le, ← coeff_subst_X_pow_mul φ g hφ0 q, hES]
  have hc : PowerSeries.constantCoeff g = π (PowerSeries.coeff q (F.nthSeries q)) := by
    have := congrArg (PowerSeries.coeff q) hg
    rw [PowerSeries.coeff_map, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    exact this.symm
  have hc' : PowerSeries.constantCoeff g' = π (PowerSeries.coeff q (F'.nthSeries q)) := by
    have := congrArg (PowerSeries.coeff q) hg'
    rw [PowerSeries.coeff_map, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    exact this.symm
  rw [hc, hc'] at key
  have hu : π (↑(uU⁻¹) : R) * π ↑uU = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hu' : (π (↑(uU⁻¹) : R) * π ↑uU) ^ q = 1 := by rw [hu, one_pow]
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hπ]
  rw [map_sub, map_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  linear_combination (-(π (↑(uU⁻¹) : R)) ^ q) * key + (-(π (PowerSeries.coeff q (F.nthSeries q)))) * hu'

end S_FormalGroup_exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso
end P2MW
export P2MW.S_FormalGroup_exists_isUnit_coeff_nthSeries_sub_mul_coeff_nthSeries_mem_span_of_lawIso (solution)
