-- Prove2me | solution 1 for Erdos287.dense_prime_power_endpoint_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:50:27.524421+00:00
-- url     : https://prove2.me/submissions/2bef0190-ae37-4a79-9436-272d1bb29261

import Mathlib
import Theorems.Thm_Erdos287_sparse_prime_power_layer

open Finset

set_option autoImplicit false

/-- Endpoint restrictions when the denominator interval has ratio below
three. A prime power at the minimum can only come from the cancellation
at three. A prime power of cofactor at most three at the maximum has
just two possibilities. -/
theorem solution (D : Finset ℕ) (m M p e : ℕ) (hm : 0 < m) (hp : p.Prime) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hmD : m ∈ D) (hMD : M ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) (hratio : M < 3 * m) :
    (m = p ^ e → p = 3 ∧ 2 * m ∈ D) ∧
    (p ^ e ∣ M → M ≤ 3 * p ^ e →
      (p = 3 ∧ M = 2 * p ^ e ∧ p ^ e ∈ D) ∨
      (p = 5 ∧ M = 3 * p ^ e ∧ 2 * p ^ e ∈ D)) := by
  let q := p ^ e
  let H := D.filter (fun n => q ∣ n)
  have hq : 0 < q := pow_pos hp.pos _
  have hH : H ⊆ D := filter_subset _ _
  have hbelow (n : ℕ) (hn : n ∈ H) : n ≤ M := (mem_Icc.mp (hD (hH hn))).2
  have hclass (hspan : M < m + 2 * q) (hmax : M < 4 * q) :
      H = ∅ ∨ (p = 3 ∧ H = {q, 2 * q}) ∨ (p = 5 ∧ H = {2 * q, 3 * q}) :=
    Erdos287.sparse_prime_power_layer D m M p e hm hp he hD hsum hspan hmax
  constructor
  · intro hmin
    change m = q at hmin
    have hmem : q ∈ H := mem_filter.mpr ⟨hmin ▸ hmD, dvd_rfl⟩
    rcases hclass (by omega) (by omega) with h | ⟨hp3, h⟩ | ⟨hp5, h⟩
    · simp [h] at hmem
    · have htwo : 2 * q ∈ H := by rw [h]; simp
      exact ⟨hp3, hmin.symm ▸ hH htwo⟩
    · have hthree : 3 * q ∈ H := by rw [h]; simp
      have := hbelow _ hthree
      omega
  · intro hd hsize
    change q ∣ M at hd
    change M ≤ 3 * q at hsize
    change (p = 3 ∧ M = 2 * q ∧ q ∈ D) ∨ (p = 5 ∧ M = 3 * q ∧ 2 * q ∈ D)
    have hmem : M ∈ H := mem_filter.mpr ⟨hMD, hd⟩
    rcases hclass (by omega) (by omega) with h | ⟨hp3, h⟩ | ⟨hp5, h⟩
    · simp [h] at hmem
    · have hone : q ∈ H := by rw [h]; simp
      have htwo : 2 * q ∈ H := by rw [h]; simp
      rw [h, mem_insert, mem_singleton] at hmem
      exact Or.inl ⟨hp3, hmem.resolve_left (by have := hbelow _ htwo; omega), hH hone⟩
    · have htwo : 2 * q ∈ H := by rw [h]; simp
      have hthree : 3 * q ∈ H := by rw [h]; simp
      rw [h, mem_insert, mem_singleton] at hmem
      exact Or.inr ⟨hp5, hmem.resolve_left (by have := hbelow _ hthree; omega), hH htwo⟩

