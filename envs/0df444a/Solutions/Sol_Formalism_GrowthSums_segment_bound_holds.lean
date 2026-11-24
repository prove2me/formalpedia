-- Prove2me | solution 1 for Formalism.GrowthSums.segment_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:06.40656+00:00
-- url     : https://prove2.me/submissions/a11fb98e-8fbc-46eb-9fa9-fcf37179f25d

import Definitions.Def_Formalism_GrowthSums_StatementB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Segment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
open Formalism.G0
namespace Formalism.GrowthSums
theorem _root_.solution : SegmentBound := by
  intro n T L₂ K r u M₀ G' N₁ hr hu hn hG hT hgood s s' f f' hs hs' hm hm' hsucc hf hfim hf' hfim'
  obtain ⟨_, hTiles, hInt⟩ := hgood
  intro a b D
  have haT : a ∈ T ∩ Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)) := by
    rw [hfim]; exact mem_image_of_mem _ (mem_univ _)
  have hbT : b ∈ T ∩ Ico (s' * ((6 * r + 1) * u)) ((s' + 1) * ((6 * r + 1) * u)) := by
    rw [hfim']; exact mem_image_of_mem _ (mem_univ _)
  have hD : D = if s < s' then b - a else b + n - a := rfl
  clear_value a b D
  set E := (6 * r + 1) * u with hEdef
  set t := n / E with htdef
  have hE : 0 < E := Nat.mul_pos (by omega) (by omega)
  have ht1 : M₀ + 1 ≤ t := (Nat.le_div_iff_mul_le hE).2 hn
  have htE : t * E ≤ n := Nat.div_mul_le_self n E
  have hnE : n < t * E + E := by
    have h1 : E * t + n % E = n := Nat.div_add_mod n E
    have h2 := Nat.mod_lt n hE
    rw [mul_comm] at h1
    omega
  rw [mem_inter, mem_Ico] at haT hbT
  obtain ⟨haT, ha1, ha2⟩ := haT
  obtain ⟨hbT, hb1, hb2⟩ := hbT
  rw [add_one_mul] at ha2 hb2

  have hgap : (if s < s' then s' - s else s' + t - s) ≤ M₀ + 1 := by
    obtain ⟨j, hj, hmj⟩ := hTiles ((s + 1) % t) (Nat.mod_lt _ (by omega))
    rw [Nat.mod_add_mod, show s + 1 + j = s + (j + 1) by omega] at hmj
    by_contra hc
    exact hsucc (j + 1) (by omega) (by omega) hmj

  have hst : (s + 1) * E ≤ t * E := Nat.mul_le_mul_right _ (by omega)
  have hs't : (s' + 1) * E ≤ t * E := Nat.mul_le_mul_right _ (by omega)
  rw [add_one_mul] at hst hs't
  have hGE : M₀ * E + 5 * E ≤ G' := by rw [← add_mul]; exact hG
  have hDG : D < G' ∧ (a + D) % n = b := by
    by_cases hss : s < s'
    · rw [if_pos hss] at hgap hD
      have hg : s' * E = s * E + (s' - s) * E := by rw [← add_mul]; congr 1; omega
      have hgE : (s' - s) * E ≤ M₀ * E + E := by
        rw [← add_one_mul]; exact Nat.mul_le_mul_right _ hgap
      have hsE : s * E + E ≤ s' * E := by rw [← add_one_mul]; exact Nat.mul_le_mul_right _ hss
      refine ⟨by omega, ?_⟩
      rw [hD, show a + (b - a) = b by omega]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [if_neg hss] at hgap hD
      have hg : s' * E + t * E = s * E + (s' + t - s) * E := by
        rw [← add_mul, ← add_mul]; congr 1; omega
      have hgE : (s' + t - s) * E ≤ M₀ * E + E := by
        rw [← add_one_mul]; exact Nat.mul_le_mul_right _ hgap
      refine ⟨by omega, ?_⟩
      rw [hD, show a + (b + n - a) = b + n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hDG.1, hDG.2, ?_⟩
  calc (T ∩ (range (D + 1)).image (fun j => (a + j) % n)).card
      ≤ (T ∩ window n a G').card := by
        apply card_le_card
        apply inter_subset_inter_left
        unfold window
        apply image_subset_image
        have h3 := hDG.1
        intro x hx
        rw [mem_range] at hx ⊢
        omega
    _ ≤ N₁ := hInt a (by omega)
end Formalism.GrowthSums
