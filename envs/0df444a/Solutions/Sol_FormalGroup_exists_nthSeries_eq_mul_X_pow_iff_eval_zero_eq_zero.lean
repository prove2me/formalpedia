-- Prove2me | solution 1 for FormalGroup.exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b6acd117-35cc-5882-a3d9-d1c542877d19

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_FormalGroup_coeff_one_nthSeries
import Theorems.Thm_FormalGroup_exists_nthSeries_eq_qfold_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero

set_option autoImplicit false

open PowerSeries Polynomial

namespace R4IgusaOrigin

variable {T : Type*} [CommRing T]

theorem coeff_one_X_mul_coe_mul (g : T[X]) (v : T⟦X⟧) :
    PowerSeries.coeff 1 (PowerSeries.X * (g : T⟦X⟧) * v) = g.coeff 0 * PowerSeries.constantCoeff v := by
  rw [mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply (g : T⟦X⟧), Polynomial.coeff_coe]

theorem coeff_X_mul_coe_mul_sub_mem (I : Ideal T) (q : ℕ) (hq : 1 ≤ q) (g : T[X]) (hmonic : g.Monic)
    (hdeg : g.natDegree = q - 1) (hdist : ∀ i < q - 1, g.coeff i ∈ I) (v : T⟦X⟧) :
    PowerSeries.coeff q (PowerSeries.X * (g : T⟦X⟧) * v) - PowerSeries.constantCoeff v ∈ I := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hdeg hdist
  rw [mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul]
  have hmem : (n, 0) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  rw [← Finset.add_sum_erase _ _ hmem]
  have hlead : PowerSeries.coeff n (g : T⟦X⟧) = 1 := by
    rw [Polynomial.coeff_coe, ← hdeg]; exact hmonic
  rw [hlead, one_mul, PowerSeries.coeff_zero_eq_constantCoeff, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hp' := Finset.mem_erase.mp hp
  have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp'.2
  have hlt : p.1 < n := by
    rcases Nat.lt_or_ge p.1 n with h | h
    · exact h
    · exfalso
      apply hp'.1
      have h1 : p.1 = n := by omega
      have h2 : p.2 = 0 := by omega
      exact Prod.ext h1 h2
  rw [Polynomial.coeff_coe]
  exact Ideal.mul_mem_right _ _ (hdist _ hlt)

theorem X_mul_cancel {a b : T⟦X⟧} (h : PowerSeries.X * a = PowerSeries.X * b) : a = b := by
  ext n
  have := congrArg (PowerSeries.coeff (n + 1)) h
  simpa only [PowerSeries.coeff_succ_X_mul] using this

end R4IgusaOrigin

open IsLocalRing Polynomial in

theorem solution
    (T : Type*) [CommRing T] [IsLocalRing T]
    (F : FormalGroup T) [F.IsComm] (q : ℕ) [Fact q.Prime]
    (g : T[X]) (hmonic : g.Monic) (hdeg : g.natDegree = q - 1)
    (hdist : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v) :
    ((∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ q) ↔ g.eval 0 = 0) ∧
      (g.eval 0 = 0 ↔ (q : T) = 0) := by
  have hqprime : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hqprime.two_le
  have hv0 : IsUnit (PowerSeries.constantCoeff v) := PowerSeries.isUnit_iff_constantCoeff.mp hv

  have hlin : (q : T) = g.coeff 0 * PowerSeries.constantCoeff v := by
    rw [← F.coeff_one_nthSeries q, hF, R4IgusaOrigin.coeff_one_X_mul_coe_mul]
  have heval : g.eval 0 = g.coeff 0 := (Polynomial.coeff_zero_eq_eval_zero g).symm

  have hiff2 : g.eval 0 = 0 ↔ (q : T) = 0 := by
    rw [heval]
    constructor
    · intro h
      rw [hlin, h, zero_mul]
    · intro h
      rw [h] at hlin
      exact (hv0.mul_left_eq_zero.mp hlin.symm)
  refine ⟨⟨?_, ?_⟩, hiff2⟩
  ·
    rintro ⟨u, hu, hu'⟩
    have hq1 : q = (q - 1) + 1 := by omega
    have hcancel : (g : T⟦X⟧) * v = u * PowerSeries.X ^ (q - 1) := by
      apply R4IgusaOrigin.X_mul_cancel
      calc PowerSeries.X * ((g : T⟦X⟧) * v) = F.nthSeries q := by rw [hF, mul_assoc]
        _ = u * PowerSeries.X ^ q := hu'
        _ = PowerSeries.X * (u * PowerSeries.X ^ (q - 1)) := by
            conv_lhs => rw [hq1]
            ring
    have hcc := congrArg PowerSeries.constantCoeff hcancel
    rw [map_mul, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega : q - 1 ≠ 0), mul_zero,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply (g : T⟦X⟧), Polynomial.coeff_coe] at hcc
    rw [heval]
    exact hv0.mul_left_eq_zero.mp hcc
  ·
    intro h
    have hqT : (q : T) = 0 := hiff2.mp h

    have hchar : CharP (ResidueField T) q := by
      refine (CharP.charP_iff_prime_eq_zero hqprime).mpr ?_
      rw [← map_natCast (residue T) q, hqT, map_zero]
    have hunit : ∀ k : ℕ, 1 ≤ k → ¬ q ∣ k → IsUnit (k : T) := by
      intro k _ hndvd
      rw [← residue_ne_zero_iff_isUnit, map_natCast]
      intro hk
      exact hndvd ((CharP.cast_eq_zero_iff (ResidueField T) q k).mp hk)
    obtain ⟨hh, G, hqfold⟩ := F.exists_nthSeries_eq_qfold_of_isUnit hq2 hunit
    have hXq : F.nthSeries q = PowerSeries.X ^ q * G := by
      rw [hqfold, ← Nat.cast_smul_eq_nsmul T q, hqT, zero_smul, zero_smul, zero_add, zero_add]
    refine ⟨G, ?_, by rw [hXq, mul_comm]⟩
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hGc : PowerSeries.constantCoeff G = PowerSeries.coeff q (F.nthSeries q) := by
      rw [hXq, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hGc, hF, ← residue_ne_zero_iff_isUnit]
    have hmem := R4IgusaOrigin.coeff_X_mul_coe_mul_sub_mem (maximalIdeal T) q (by omega) g hmonic hdeg hdist v
    have hres : residue T (PowerSeries.coeff q (PowerSeries.X * (g : T⟦X⟧) * v)) =
        residue T (PowerSeries.constantCoeff v) := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hmem
    rw [hres, residue_ne_zero_iff_isUnit]
    exact hv0

end S_FormalGroup_exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero
end P2MW
export P2MW.S_FormalGroup_exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero (solution)
