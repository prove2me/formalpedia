-- Prove2me | solution 1 for FuzzyGames.NTUCore.eq_7_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:45:40.753816+00:00
-- url     : https://prove2.me/submissions/1380d544-1701-412f-8f7a-908fae201f55

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore.Aux
open FuzzyGames.NTUCore

theorem mem_piV {n : ℕ} (𝒞 : CoalFamily n) (V : Finset (Fin n) → Set (Fin n → ℝ))
    (τ x : Fin n → ℝ) :
    x ∈ piV 𝒞 V τ ↔ ∃ m ∈ balances 𝒞 τ, ∃ w : Finset (Fin n) → Fin n → ℝ,
      (∀ A ∈ 𝒞.C, w A ∈ V A) ∧ ∑ A ∈ 𝒞.C, m A • w A = x := by
  classical
  unfold piV
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, hx⟩
    rw [Set.mem_finsetSum] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have : ∀ A ∈ 𝒞.C, ∃ w ∈ V A, m A • w = g A := fun A hA => by
      simpa [Set.mem_smul_set] using hg hA
    choose! w hw hw' using this
    exact ⟨m, hm, w, hw, Finset.sum_congr rfl (fun A hA => hw' A hA)⟩
  · rintro ⟨m, hm, w, hw, rfl⟩
    exact ⟨m, hm, Set.finsetSum_mem_finsetSum _ _ _ (fun A hA =>
      Set.smul_mem_smul_set (hw A hA))⟩


theorem bal_smul {n : ℕ} (𝒞 : CoalFamily n) {τ : Fin n → ℝ} {m : Finset (Fin n) → ℝ}
    (hm : m ∈ balances 𝒞 τ) {s : ℝ} (hs : 0 ≤ s) : s • m ∈ balances 𝒞 (s • τ) := by
  obtain ⟨h0, h1, h2⟩ := hm
  refine ⟨fun A => by simpa using mul_nonneg hs (h0 A), fun A hA => by simp [h1 A hA], fun i => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, h2 i]

theorem bal_add {n : ℕ} (𝒞 : CoalFamily n) {τ σ : Fin n → ℝ} {m m' : Finset (Fin n) → ℝ}
    (hm : m ∈ balances 𝒞 τ) (hm' : m' ∈ balances 𝒞 σ) : m + m' ∈ balances 𝒞 (τ + σ) := by
  obtain ⟨h0, h1, h2⟩ := hm
  obtain ⟨h0', h1', h2'⟩ := hm'
  refine ⟨fun A => by simpa using add_nonneg (h0 A) (h0' A),
    fun A hA => by simp [h1 A hA, h1' A hA], fun i => ?_⟩
  simp only [Pi.add_apply, Finset.sum_add_distrib, h2 i, h2' i]

end FuzzyGames.NTUCore.Aux

open FuzzyGames.NTUCore FuzzyGames.NTUCore.Aux in
theorem solution {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) :
    (∀ t : ℝ, 0 < t → ∀ τ ∈ orthant n, piV 𝒞 V (t • τ) = t • piV 𝒞 V τ) ∧
      (∀ τ ∈ orthant n, ∀ σ ∈ orthant n, piV 𝒞 V τ + piV 𝒞 V σ ⊆ piV 𝒞 V (τ + σ)) := by
  classical
  constructor
  · intro t ht τ _
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', mem_piV, mem_piV]
    constructor
    · rintro ⟨m, hm, w, hw, rfl⟩
      refine ⟨t⁻¹ • m, ?_, w, hw, ?_⟩
      · have := bal_smul 𝒞 hm (inv_nonneg.2 ht.le)
        rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
      · rw [Finset.smul_sum]
        apply Finset.sum_congr rfl; intro A _
        simp [smul_smul]
    · rintro ⟨m, hm, w, hw, hx⟩
      refine ⟨t • m, bal_smul 𝒞 hm ht.le, w, hw, ?_⟩
      have : x = t • (t⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
      rw [this, ← hx, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro A _
      simp [smul_smul]
  · intro τ _ σ _ z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.1 hz
    simp only [piV, Set.mem_iUnion, exists_prop] at hx hy ⊢
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨m', hm', hy⟩ := hy
    refine ⟨m + m', bal_add 𝒞 hm hm', ?_⟩
    have hset : ∑ A ∈ 𝒞.C, m A • V A + ∑ A ∈ 𝒞.C, m' A • V A =
        ∑ A ∈ 𝒞.C, (m + m') A • V A := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro A hA
      rw [Pi.add_apply, (hV.convex A hA).add_smul (hm.1 A) (hm'.1 A)]
    rw [← hset]
    exact Set.add_mem_add hx hy
