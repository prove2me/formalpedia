-- Prove2me | solution 1 for Erdos287.three_power_endpoint_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:08:21.819559+00:00
-- url     : https://prove2.me/submissions/b05a5e69-dfd6-4e49-a2ba-a50d324ddebd

import Mathlib
import Theorems.Thm_Erdos287_exceptional_endpoint_carries
import Theorems.Thm_Erdos287_sparse_prime_power_layer

open Finset

set_option autoImplicit false

/-- A forced omission at the next lower three-adic layer yields a
test on the two neighboring even denominators. -/
theorem solution (D : Finset ℕ) (m j : ℕ) (hm : 0 < m) (hj : 1 ≤ j)
    (hD : D ⊆ Finset.Icc m (6 * 3 ^ j)) (hmD : m ∈ D) (hMD : 6 * 3 ^ j ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) (hratio : 6 * 3 ^ j < 3 * m)
    (hcover : ∀ n, m ≤ n → n + 1 ≤ 6 * 3 ^ j → n ∈ D ∨ (n + 1) ∈ D) :
    let r := 3 ^ j
    (5 * r - 1) ∈ D ∧ (5 * r + 1) ∈ D ∧
      ∀ p a : ℕ, p.Prime → 1 ≤ a → 2 * p ^ a ≠ 5 * r - 1 ∧ 2 * p ^ a ≠ 5 * r + 1 := by
  let r := 3 ^ j
  change (5 * r - 1) ∈ D ∧ (5 * r + 1) ∈ D ∧
    ∀ p a : ℕ, p.Prime → 1 ≤ a → 2 * p ^ a ≠ 5 * r - 1 ∧ 2 * p ^ a ≠ 5 * r + 1
  change 6 * r < 3 * m at hratio
  have hr : 3 ≤ r := by
    simpa only [pow_one, r] using Nat.pow_le_pow_right (by decide : 0 < 3) hj
  obtain ⟨h4, h5⟩ := (Erdos287.exceptional_endpoint_carries D m (6 * 3 ^ j) j
    hm hj hD hmD hMD hsum hratio).1 rfl
  change 4 * r ∈ D at h4
  change 5 * r ∉ D at h5
  have hm4 : m ≤ 4 * r := (mem_Icc.mp (hD h4)).1
  have hprev : (5 * r - 1) + 1 = 5 * r := by omega
  have hleft : (5 * r - 1) ∈ D := by
    apply (hcover (5 * r - 1) (by omega) (by omega : (5 * r - 1) + 1 ≤ 6 * r)).resolve_right
    rwa [hprev]
  have hright : (5 * r + 1) ∈ D :=
    (hcover (5 * r) (by omega) (by omega : 5 * r + 1 ≤ 6 * r)).resolve_left h5
  refine ⟨hleft, hright, ?_⟩
  intro p a hp ha
  let q := p ^ a
  have hforbid (hx : 2 * r < q) (hy : q < 3 * r) (hqD : 2 * q ∈ D) : False := by
    have hq : 2 * q ∈ D.filter (fun n => q ∣ n) := mem_filter.mpr ⟨hqD, dvd_mul_left q 2⟩
    rcases Erdos287.sparse_prime_power_layer D m (6 * r) p a hm hp ha hD hsum
      (by omega : 6 * r < m + 2 * q) (by omega : 6 * r < 4 * q) with he | ⟨hp3, _⟩ | ⟨_, he⟩
    · change D.filter (fun n => q ∣ n) = ∅ at he
      simp [he] at hq
    · have hqp : q = 3 ^ a := by simp [q, hp3]
      by_cases hle : a ≤ j
      · have hleR : 3 ^ a ≤ r := Nat.pow_le_pow_right (by decide : 0 < 3) hle
        omega
      · have hge : 3 ^ (j + 1) ≤ 3 ^ a := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega)
        have hpow : 3 ^ (j + 1) = 3 * r := pow_succ' _ _
        omega
    · change D.filter (fun n => q ∣ n) = {2 * q, 3 * q} at he
      have h3q : 3 * q ∈ D.filter (fun n => q ∣ n) := by rw [he]; simp
      have h3M : 3 * q ≤ 6 * r := (mem_Icc.mp (hD (mem_filter.mp h3q).1)).2
      omega
  constructor
  · intro h
    change 2 * q = 5 * r - 1 at h
    exact hforbid (by omega) (by omega) (h.symm ▸ hleft)
  · intro h
    change 2 * q = 5 * r + 1 at h
    exact hforbid (by omega) (by omega) (h.symm ▸ hright)

