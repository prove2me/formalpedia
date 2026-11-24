-- Prove2me | solution 1 for Formalism.GrowthSums.top_count_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:06.858436+00:00
-- url     : https://prove2.me/submissions/6756dd28-1188-4f4c-89d5-62bf24a06628

import Definitions.Def_Formalism_GrowthSums_StatementB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_NextEvenTopHolds
import Theorems.Thm_Formalism_GrowthSums_next_even_top_holds

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
theorem _root_.solution : TopCount := by
  intro n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood
  have hnext := next_even_top_holds n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood
  obtain ⟨_, _, hInt⟩ := hgood
  have hℓpos : 0 < (6 * r + 1) * u := Nat.mul_pos (by omega) (by omega)
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.mul_pos (by omega) hℓpos) hn
  have hGpos : 0 < G' := lt_of_lt_of_le (Nat.mul_pos (by omega) hℓpos) hG
  constructor
  · have hsub : range n ⊆ (T ×ˢ Icc 1 G').image (fun p => (p.1 + n * G' - p.2) % n) := by
      intro i hi
      rw [mem_range] at hi
      obtain ⟨D, hD, hDT, -⟩ := hnext i hi
      rw [mem_Icc] at hD
      rw [mem_image]
      refine ⟨((i + D) % n, D), mem_product.2 ⟨hDT, mem_Icc.2 hD⟩, ?_⟩
      simp only
      have h1 := Nat.div_add_mod (i + D) n
      obtain ⟨q, hq⟩ : ∃ q, q = (i + D) / n := ⟨_, rfl⟩
      obtain ⟨x, hx⟩ : ∃ x, x = (i + D) % n := ⟨_, rfl⟩
      rw [← hq, ← hx] at h1
      rw [← hx]
      have hqG : q ≤ G' := by
        by_contra hc
        have : n * (G' + 1) ≤ n * q := Nat.mul_le_mul_left _ (by omega)
        have : n * (G' + 1) = n * G' + n := by ring
        have : G' ≤ n * G' := Nat.le_mul_of_pos_left _ hnpos
        omega
      have h2 : n * (G' - q) = n * G' - n * q := Nat.mul_sub n G' q
      have h3 : n * q ≤ n * G' := Nat.mul_le_mul_left _ hqG
      have h4 : x + n * G' - D = i + n * (G' - q) := by omega
      rw [h4, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    calc n = (range n).card := (card_range n).symm
      _ ≤ _ := card_le_card hsub
      _ ≤ (T ×ˢ Icc 1 G').card := card_image_le
      _ = T.card * G' := by rw [card_product, Nat.card_Icc]; simp
  · have hcov : T ⊆ (T.image (fun p => p / G')).biUnion
        (fun c => T ∩ window n (c * G') G') := by
      intro p hp
      rw [mem_biUnion]
      refine ⟨p / G', mem_image_of_mem _ hp, mem_inter.2 ⟨hp, ?_⟩⟩
      have hpn : p < n := mem_range.1 (hT hp)
      unfold window
      rw [mem_image]
      have h1 := Nat.lt_div_mul_add (a := p) hGpos
      have h2 := Nat.div_mul_le_self p G'
      refine ⟨p - p / G' * G', mem_range.2 (by omega), ?_⟩
      rw [show p / G' * G' + (p - p / G' * G') = p by omega, Nat.mod_eq_of_lt hpn]
    have hcard : T.card ≤ (T.image (fun p => p / G')).card * N₁ := by
      calc T.card ≤ _ := card_le_card hcov
        _ ≤ ∑ c ∈ T.image (fun p => p / G'), (T ∩ window n (c * G') G').card :=
            card_biUnion_le
        _ ≤ ∑ c ∈ T.image (fun p => p / G'), N₁ := by
            apply sum_le_sum
            intro c hc
            obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
            apply hInt
            have := Nat.div_mul_le_self p G'
            have := mem_range.1 (hT hp)
            omega
        _ = _ := by rw [sum_const, smul_eq_mul]
    have himg : (T.image (fun p => p / G')).card ≤ n / G' + 1 := by
      calc _ ≤ (range (n / G' + 1)).card := by
            apply card_le_card
            intro c hc
            obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
            rw [mem_range]
            have := Nat.div_le_div_right (c := G') (mem_range.1 (hT hp)).le
            omega
        _ = _ := card_range _
    have h5 : (n / G' + 1) * G' ≤ n + G' := by
      have := Nat.div_mul_le_self n G'
      rw [add_mul, one_mul]; omega
    calc T.card * G' ≤ ((n / G' + 1) * N₁) * G' :=
          Nat.mul_le_mul_right _ (hcard.trans (Nat.mul_le_mul_right _ himg))
      _ = N₁ * ((n / G' + 1) * G') := by ring
      _ ≤ N₁ * (n + G') := Nat.mul_le_mul_left _ h5
end Formalism.GrowthSums
