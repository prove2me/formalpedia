-- Prove2me | solution 1 for FairShareAlmostAll.Slack.enough_buffers
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:48:25.305133+00:00
-- url     : https://prove2.me/submissions/2e3c67dd-3317-484a-8ea8-a7f3812540e6

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

open FairShareAlmostAll.Slack

namespace EnoughBuffersAux

theorem rank_card {m : ℕ} (s : Finset (Fin m)) (k : ℕ) (hk : k ≤ s.card) :
    (s.filter (fun g => (s.filter (fun r => r < g)).card < k)).card = k := by
  classical
  have hmono : ∀ a ∈ s, ∀ b ∈ s, a < b →
      (s.filter (fun r => r < a)).card < (s.filter (fun r => r < b)).card := by
    intro a ha b hb hab
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨a, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hab⟩
    · simp [ha, hab]
    · simp
  have hinj : Set.InjOn (fun g => (s.filter (fun r => r < g)).card) s := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (hmono a ha b hb h).ne
    · exact h
    · exact absurd hab (hmono b hb a ha h).ne'
  have hsub : s.image (fun g => (s.filter (fun r => r < g)).card) ⊆ Finset.range s.card := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    simp only [Finset.mem_range]
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨g, hg, by simp⟩
  have himg : s.image (fun g => (s.filter (fun r => r < g)).card) = Finset.range s.card :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_range, Finset.card_image_of_injOn hinj])
  have hfin : (s.filter (fun g => (s.filter (fun r => r < g)).card < k)).image
      (fun g => (s.filter (fun r => r < g)).card) = Finset.range k := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨g, ⟨_, hg⟩, rfl⟩
      exact hg
    · intro hx
      have hx' : x ∈ s.image (fun g => (s.filter (fun r => r < g)).card) := by
        rw [himg, Finset.mem_range]; omega
      simp only [Finset.mem_image] at hx'
      obtain ⟨g, hg, hgx⟩ := hx'
      exact ⟨g, ⟨hg, hgx ▸ hx⟩, hgx⟩
  rw [← Finset.card_image_of_injOn (hinj.mono (by
    intro x hx; exact (Finset.mem_filter.mp hx).1)), hfin, Finset.card_range]

theorem mem_bucket {q m h : ℕ} (g : Fin m) :
    g ∈ bucket q m h ↔ prefixSize q (h - 1) ≤ g.val ∧ g.val < prefixSize q h := by
  unfold bucket
  simp

theorem mem_reserve {q m : ℕ} (g : Fin m) : g ∈ reserve q m ↔ g.val % q = 0 := by
  unfold reserve
  simp

theorem available_card {q m h : ℕ} (hq : 2 ≤ q) :
    (bucket q m h).card / q ≤ (bucket q m h \ reserve q m).card := by
  classical
  set a := prefixSize q (h - 1)
  set L := (bucket q m h).card
  have hL : L ≤ min (prefixSize q h) m - a := by
    have hsub : (bucket q m h).map Fin.valEmbedding ⊆ Finset.Ico a (min (prefixSize q h) m) := by
      intro x hx
      simp only [Finset.mem_map, Fin.valEmbedding_apply] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      rw [mem_bucket] at hg
      simp only [Finset.mem_Ico]
      have := g.isLt
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_map, Nat.card_Ico] at this
    exact this
  set c : ℕ := if a % q = 0 then 1 else 0 with hc
  have hc1 : c ≤ 1 := by rw [hc]; split_ifs <;> omega
  have hqpos : 0 < q := by omega
  have himage : (Finset.range (L / q)).image (fun t => a + c + t * q) ⊆
      (bucket q m h \ reserve q m).map Fin.valEmbedding := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have ht' : (t + 1) * q ≤ L := (Nat.le_div_iff_mul_le hqpos).mp ht
    have hmod : (a + c + t * q) % q ≠ 0 := by
      rw [Nat.add_mul_mod_self_right]
      rw [hc]
      split_ifs with h0
      · rw [Nat.add_mod, h0]
        simp
        omega
      · simpa using h0
    have hlt : a + c + t * q < min (prefixSize q h) m := by
      have : t * q + q ≤ L := by rw [Nat.add_mul, one_mul] at ht'; exact ht'
      generalize t * q = u at *
      omega
    simp only [Finset.mem_map, Fin.valEmbedding_apply]
    refine ⟨⟨a + c + t * q, by omega⟩, ?_, rfl⟩
    rw [Finset.mem_sdiff, mem_bucket, mem_reserve]
    refine ⟨⟨?_, ?_⟩, hmod⟩
    · show a ≤ a + c + t * q
      omega
    · show a + c + t * q < prefixSize q h
      omega
  have hinj : Set.InjOn (fun t => a + c + t * q) (Finset.range (L / q) : Set ℕ) := by
    intro x _ y _ hxy
    simp only at hxy
    have : x * q = y * q := by omega
    exact Nat.eq_of_mul_eq_mul_right hqpos this
  have := Finset.card_le_card himage
  rw [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_map] at this
  exact this

theorem buffer_card {q m h : ℕ} (hq : 2 ≤ q) :
    (bucket q m h).card / q = (buffer q m h).card := by
  classical
  have hbuf : buffer q m h = (bucket q m h \ reserve q m).filter (fun g =>
      ((bucket q m h \ reserve q m).filter (fun r => r < g)).card < (bucket q m h).card / q) := by
    unfold buffer
    rfl
  rw [hbuf, rank_card _ _ (available_card hq)]

end EnoughBuffersAux

open EnoughBuffersAux in
theorem solution {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q)
    (j : ℕ) (hj : j ∈ Finset.Ico 1 (bucketCount q m)) :
    ((active X).filter (fun i => cutoff X q i = j)).card ≤ (bucket q m j).card / q ∧
    (bucket q m j).card / q = (buffer q m j).card := by
  classical
  obtain ⟨_, hq16, htot, _, _, _⟩ := h
  have hq2 : 2 ≤ q := by omega
  have hqpos : 0 < q := by omega
  refine ⟨?_, buffer_card hq2⟩
  rw [Finset.mem_Ico] at hj
  set F := (active X).filter (fun i => cutoff X q i = j)
  set L := (bucket q m j).card
  have hkey : ∀ i ∈ F, (q : ℝ) ≤ (L : ℝ) * X.entitlement i := by
    intro i hi
    have hci : cutoff X q i = j := (Finset.mem_filter.mp hi).2
    have hne : {h : ℕ | 1 ≤ h ∧ h ≤ bucketCount q m ∧
        (h = bucketCount q m ∨ (bucket q m h).card ≥ (q : ℝ) / X.entitlement i)}.Nonempty :=
      ⟨bucketCount q m, by omega, le_refl _, Or.inl rfl⟩
    have hmem := Nat.sInf_mem hne
    have hcut : cutoff X q i = sInf {h : ℕ | 1 ≤ h ∧ h ≤ bucketCount q m ∧
        (h = bucketCount q m ∨ (bucket q m h).card ≥ (q : ℝ) / X.entitlement i)} := rfl
    rw [← hcut, hci] at hmem
    obtain ⟨_, _, hor⟩ := hmem
    rcases hor with hor | hor
    · omega
    · have hb := X.entitlement_pos i
      rw [ge_iff_le, div_le_iff₀ hb] at hor
      exact hor
  have hsum : (F.card : ℝ) * q ≤ L := by
    have h1 : ∑ i ∈ F, (q : ℝ) ≤ ∑ i ∈ F, (L : ℝ) * X.entitlement i := Finset.sum_le_sum hkey
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
    have h2 : ∑ i ∈ F, X.entitlement i ≤ totalEntitlement X := by
      unfold totalEntitlement
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => (X.entitlement_pos i).le)
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    calc (F.card : ℝ) * q ≤ L * ∑ i ∈ F, X.entitlement i := h1
      _ ≤ L * 1 := mul_le_mul_of_nonneg_left (h2.trans htot) hL0
      _ = L := mul_one _
  have hsumN : F.card * q ≤ L := by exact_mod_cast hsum
  exact (Nat.le_div_iff_mul_le hqpos).mpr hsumN
