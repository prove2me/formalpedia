-- Prove2me | solution 1 for DeletedPrimes.share_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:12:46.203771+00:00
-- url     : https://prove2.me/submissions/d4f52588-5ae2-4e7d-bf10-05c3bbc1dfdc

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {L w : ℝ} (hL : 0 < L) (ℓ : Fin k → ℝ)
    (hℓ : ∀ i, L / k ≤ ℓ i ∧ ℓ i ≤ (1 + w) * L / k) (i : Fin k) :
    L ≤ ∑ i', ℓ i' ∧ |ℓ i / ∑ i', ℓ i' - 1 / k| ≤ w / k := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hsum : L ≤ ∑ i', ℓ i' := by
    calc L = ∑ _i' : Fin k, L / k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
      _ ≤ ∑ i', ℓ i' := Finset.sum_le_sum fun i' _ => (hℓ i').1
  refine ⟨hsum, ?_⟩
  have hspos : 0 < ∑ i', ℓ i' := lt_of_lt_of_le hL hsum
  have hpair : ∀ i', |ℓ i - ℓ i'| ≤ w * L / k := by
    intro i'
    have h1 := hℓ i; have h2 := hℓ i'
    have e : (1 + w) * L / k - L / k = w * L / k := by ring
    rw [abs_le]; constructor <;> linarith
  have hdiff : |(k : ℝ) * ℓ i - ∑ i', ℓ i'| ≤ w * L := by
    have e : (k : ℝ) * ℓ i - ∑ i', ℓ i' = ∑ i', (ℓ i - ℓ i') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [e]
    calc |∑ i', (ℓ i - ℓ i')| ≤ ∑ i', |ℓ i - ℓ i'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i' : Fin k, w * L / k := Finset.sum_le_sum fun i' _ => hpair i'
      _ = w * L := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have e2 : ℓ i / ∑ i', ℓ i' - 1 / k = ((k : ℝ) * ℓ i - ∑ i', ℓ i') / (k * ∑ i', ℓ i') := by
    field_simp
  rw [e2, abs_div, abs_of_pos (mul_pos hkpos hspos), div_le_div_iff₀ (mul_pos hkpos hspos) hkpos]
  have hw : 0 ≤ w * L := le_trans (abs_nonneg _) hdiff
  calc |(k : ℝ) * ℓ i - ∑ i', ℓ i'| * k ≤ w * L * k := mul_le_mul_of_nonneg_right hdiff hkpos.le
    _ ≤ w * (k * ∑ i', ℓ i') := by
        have : w * L * k = (w * L) * k := rfl
        nlinarith [mul_le_mul_of_nonneg_left hsum (le_of_lt hkpos), hw]
end DeletedPrimes
