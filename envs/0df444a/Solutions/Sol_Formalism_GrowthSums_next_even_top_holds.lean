-- Prove2me | solution 1 for Formalism.GrowthSums.next_even_top_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:23.700131+00:00
-- url     : https://prove2.me/submissions/8d174ddc-d71e-4bce-b5df-803f854e5605

import Definitions.Def_Formalism_GrowthSums_StatementB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_NextEvenTopHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
open Formalism.G0
namespace Formalism.GrowthSums
theorem _root_.solution : NextEvenTop := by
  intro n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood i hi
  obtain ⟨_, hTiles, _⟩ := hgood
  set ℓ := (6 * r + 1) * u with hℓ
  have hℓpos : 0 < ℓ := Nat.mul_pos (by omega) (by omega)
  have h2u : 2 * u ≤ ℓ := by rw [hℓ]; nlinarith
  set t := n / ℓ with ht
  have htM : M₀ + 1 ≤ t := (Nat.le_div_iff_mul_le hℓpos).2 hn
  have hnt : n < t * ℓ + ℓ := by
    have h1 : ℓ * t + n % ℓ = n := Nat.div_add_mod n ℓ
    have h2 := Nat.mod_lt n hℓpos
    have h3 : t * ℓ = ℓ * t := Nat.mul_comm _ _
    omega
  obtain ⟨si, hsi_lt, hsi_le, hsi_case⟩ :
      ∃ si, si < t ∧ si * ℓ ≤ i ∧ (i < si * ℓ + ℓ ∨ si + 1 = t) := by
    by_cases hc : i < t * ℓ
    · refine ⟨i / ℓ, ?_, Nat.div_mul_le_self i ℓ, Or.inl ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hℓpos).2 hc
      · exact Nat.lt_div_mul_add hℓpos
    · refine ⟨t - 1, by omega, ?_, Or.inr (by omega)⟩
      have : (t - 1) * ℓ ≤ t * ℓ := Nat.mul_le_mul_right _ (by omega)
      omega
  have htpos : 0 < t := by omega
  obtain ⟨j, hj, hM⟩ := hTiles ((si + 1) % t) (Nat.mod_lt _ htpos)
  rw [Nat.mod_add_mod] at hM
  obtain ⟨s, hs⟩ : ∃ s, s = (si + 1 + j) % t := ⟨_, rfl⟩
  rw [← hs] at hM
  have hslt : s < t := hs ▸ Nat.mod_lt _ htpos
  have hsc : s = si + 1 + j ∨ s + t = si + 1 + j := by
    by_cases hc : si + 1 + j < t
    · left; rw [hs, Nat.mod_eq_of_lt hc]
    · right
      rw [hs, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  obtain ⟨x, hx, hxe⟩ := (hM 2 (by omega) (by omega)).2 even_two
  have hxmem : x ∈ T ∩ cell r u s 2 := by rw [hx]; exact mem_singleton_self x
  rw [mem_inter] at hxmem
  obtain ⟨hxT, hxc⟩ := hxmem
  simp only [cell, mem_Ico] at hxc
  rw [← hℓ] at hxc
  have hxn : x < n := mem_range.1 (hT hxT)
  have hjl : j * ℓ ≤ M₀ * ℓ := Nat.mul_le_mul_right _ hj
  have hG5 : (M₀ + 5) * ℓ = M₀ * ℓ + 5 * ℓ := by ring
  have key : ∃ D, 1 ≤ D ∧ D ≤ G' ∧ (i + D) % n = x := by
    rcases hsc with hA | hB
    · have e : s * ℓ = si * ℓ + ℓ + j * ℓ := by rw [hA]; ring
      refine ⟨x - i, by omega, by omega, ?_⟩
      rw [show i + (x - i) = x by omega, Nat.mod_eq_of_lt hxn]
    · have e : s * ℓ + t * ℓ = si * ℓ + ℓ + j * ℓ := by rw [← add_mul, hB]; ring
      have hssi : s ≤ si := by omega
      have e2 : s * ℓ ≤ si * ℓ := Nat.mul_le_mul_right _ hssi
      by_cases hxi : i < x
      · refine ⟨x - i, by omega, by omega, ?_⟩
        rw [show i + (x - i) = x by omega, Nat.mod_eq_of_lt hxn]
      · refine ⟨x + n - i, by omega, by omega, ?_⟩
        rw [show i + (x + n - i) = x + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hxn]
  obtain ⟨D, hD1, hD2, hDx⟩ := key
  exact ⟨D, mem_Icc.2 ⟨hD1, hD2⟩, by rw [hDx]; exact ⟨hxT, hxe⟩⟩
end Formalism.GrowthSums
