-- Prove2me | solution 1 for FLT.OccurrenceStatement.three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ab256dda-b78f-5d19-9f00-af373f2eaac6

import Mathlib
import Definitions.Def_FormalHecke_Eigensystem
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd

open EisensteinWeightOne

namespace LaneB

lemma coeff_e1Chi3In {R : Type*} [CommRing R] (j : ℕ) :
    PowerSeries.coeff j (e1Chi3In R) = if j = 0 then 1 else ((6 * sigmaChi j : ℤ) : R) := by
  simp only [e1Chi3In, e1Chi3, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

theorem three_dvd_coeff_mul_e1Chi3In_sub {R : Type*} [CommRing R] (g : PowerSeries R) (n : ℕ) :
    (3 : R) ∣ PowerSeries.coeff n (g * e1Chi3In R) - PowerSeries.coeff n g := by
  classical
  rw [PowerSeries.coeff_mul]
  have hmem : (n, 0) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  rw [← Finset.add_sum_erase _ _ hmem, coeff_e1Chi3In, if_pos rfl, mul_one, add_sub_cancel_left]
  refine Finset.dvd_sum fun ij hij => ?_
  obtain ⟨hne, hanti⟩ := Finset.mem_erase.mp hij
  have hj : ij.2 ≠ 0 := by
    intro h0
    apply hne
    have : ij.1 = n := by simpa [h0] using Finset.HasAntidiagonal.mem_antidiagonal.mp hanti
    exact Prod.ext this h0
  rw [coeff_e1Chi3In, if_neg hj]
  refine Dvd.dvd.mul_left ?_ _
  refine ⟨((2 * sigmaChi ij.2 : ℤ) : R), ?_⟩
  push_cast
  ring

theorem three_dvd_coeff_bridgeProduct_sub {R : Type*} [CommRing R] (a : ℕ → R) (m : ℕ) :
    (3 : R) ∣ PowerSeries.coeff m (bridgeProduct a) - a m := by
  have h := three_dvd_coeff_mul_e1Chi3In_sub (PowerSeries.mk a) m
  rwa [PowerSeries.coeff_mk] at h

theorem three_dvd_natCast_sub_chiNegThree_cast (R : Type*) [CommRing R] (ℓ : ℕ) :
    (3 : R) ∣ (ℓ : R) - ((chiNegThree ℓ : ℤ) : R) := by
  have h : (3 : ℤ) ∣ (ℓ : ℤ) - chiNegThree ℓ := by
    simp only [chiNegThree]
    split_ifs <;> omega
  obtain ⟨c, hc⟩ := h
  refine ⟨(c : R), ?_⟩
  have h := congrArg (fun z : ℤ => (z : R)) hc
  push_cast at h
  convert h using 2

theorem three_dvd_coeff_heckeT_two_sub_residual {R : Type*} [CommRing R] (a : ℕ → R)
    {ℓ : ℕ} (eℓ : R)
    (hrec : ∀ n : ℕ, a (ℓ * n) + eℓ * (if ℓ ∣ n then a (n / ℓ) else 0) = a ℓ * a n)
    (n : ℕ) :
    (3 : R) ∣ (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
        - a ℓ * PowerSeries.coeff n (bridgeProduct a))
      - ((ℓ : R) - eℓ) * (if ℓ ∣ n then a (n / ℓ) else 0) := by
  have hA : ∀ m : ℕ, (3 : R) ∣ PowerSeries.coeff m (bridgeProduct a) - a m :=
    three_dvd_coeff_bridgeProduct_sub a
  have hD : (3 : R) ∣ (if ℓ ∣ n then PowerSeries.coeff (n / ℓ) (bridgeProduct a) else 0)
      - (if ℓ ∣ n then a (n / ℓ) else 0) := by
    split
    · exact hA (n / ℓ)
    · simp
  have hkey : (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
        - a ℓ * PowerSeries.coeff n (bridgeProduct a))
      - ((ℓ : R) - eℓ) * (if ℓ ∣ n then a (n / ℓ) else 0)
      = (PowerSeries.coeff (ℓ * n) (bridgeProduct a) - a (ℓ * n))
        + (ℓ : R) * ((if ℓ ∣ n then PowerSeries.coeff (n / ℓ) (bridgeProduct a) else 0)
            - (if ℓ ∣ n then a (n / ℓ) else 0))
        - a ℓ * (PowerSeries.coeff n (bridgeProduct a) - a n) := by
    rw [PowerSeries.coeff_heckeT]
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    linear_combination hrec n
  rw [hkey]
  exact dvd_sub (dvd_add (hA (ℓ * n)) (hD.mul_left (ℓ : R))) ((hA n).mul_left (a ℓ))

end LaneB

theorem solution {R : Type*} [CommRing R] {N : ℕ} {a : ℕ → R}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : R)) a)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    (3 : R) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) := by
  have hrec : ∀ m : ℕ,
      a (ℓ * m) + ((chiNegThree ℓ : ℤ) : R) * (if ℓ ∣ m then a (m / ℓ) else 0) = a ℓ * a m := by
    simpa only [if_neg hℓN] using heig.2 ℓ hℓ
  have h1 := LaneB.three_dvd_coeff_heckeT_two_sub_residual a ((chiNegThree ℓ : ℤ) : R) hrec n
  have h2 : (3 : R) ∣ ((ℓ : R) - ((chiNegThree ℓ : ℤ) : R)) * (if ℓ ∣ n then a (n / ℓ) else 0) :=
    (LaneB.three_dvd_natCast_sub_chiNegThree_cast R ℓ).mul_right _
  have hmul : (3 : R) ∣ PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
      - a ℓ * PowerSeries.coeff n (bridgeProduct a) := by
    have := dvd_add h1 h2
    simpa using this
  have hsm : PowerSeries.coeff n (a ℓ • bridgeProduct a) = a ℓ * PowerSeries.coeff n (bridgeProduct a) := by
    rw [map_smul, smul_eq_mul]
  rw [map_sub, hsm]
  exact hmul

end S_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd
end P2MW
export P2MW.S_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd (solution)
