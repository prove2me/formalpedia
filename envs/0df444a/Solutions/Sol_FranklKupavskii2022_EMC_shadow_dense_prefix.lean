-- Prove2me | solution 1 for FranklKupavskii2022.EMC.shadow_dense_prefix
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:49:16.951235+00:00
-- url     : https://prove2.me/submissions/19af21ba-c1bd-4c1a-a945-b7e0fa054b9f

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- If the `i`-th element of the sorted list of `F` is at most `N`, then `F ∩ [1, N]` has at
least `i + 1` elements. -/
theorem aux_sdp_card (F : Finset ℕ) (hF1 : ∀ x ∈ F, 1 ≤ x) (N i : ℕ)
    (hi : i < F.sort.length) (hle : F.sort.get ⟨i, hi⟩ ≤ N) :
    i + 1 ≤ (F ∩ Finset.Icc 1 N).card := by
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (i + 1))))
    (t := F ∩ Finset.Icc 1 N)
    (fun j : Fin (i + 1) => F.sort.get ⟨j.1, lt_of_le_of_lt (Nat.le_of_lt_succ j.2) hi⟩)
    (by
      intro j _
      have hmem : F.sort.get ⟨j.1, lt_of_le_of_lt (Nat.le_of_lt_succ j.2) hi⟩ ∈ F := by
        rw [← Finset.mem_sort (s := F) (r := fun a b => a ≤ b)]
        exact List.get_mem _ _
      have hmono : F.sort.get ⟨j.1, lt_of_le_of_lt (Nat.le_of_lt_succ j.2) hi⟩ ≤
          F.sort.get ⟨i, hi⟩ :=
        (F.pairwise_sort (· ≤ ·)).rel_get_of_le (by
          show j.1 ≤ i
          exact Nat.le_of_lt_succ j.2)
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_Icc]
      exact ⟨hmem, hF1 _ hmem, le_trans hmono hle⟩)
    (by
      intro a _ b _ hab
      have := (List.Nodup.get_inj_iff (F.sort_nodup (· ≤ ·))).1 hab
      exact Fin.ext (by simpa using this))
  simpa using h

/-- The explicit sorted list of the `k`-set used for residue class `j`. -/
def aux_sdp_L (k s j : ℕ) : List ℕ :=
  1 :: (List.range (k - 1)).map (fun t => max (j + t * (s + 1)) 2)

theorem aux_sdp_L_pairwise (k s j : ℕ) (hs : 1 ≤ s) (hj1 : 1 ≤ j) :
    (aux_sdp_L k s j).Pairwise (· < ·) := by
  unfold aux_sdp_L
  rw [List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨t, _, rfl⟩ := ha
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_range).imp ?_
    intro a b hab
    have h1 : (a + 1) * (s + 1) ≤ b * (s + 1) := Nat.mul_le_mul_right _ hab
    have h2 : 1 * (s + 1) ≤ b * (s + 1) := Nat.mul_le_mul_right _ (by omega)
    have h3 : (a + 1) * (s + 1) = a * (s + 1) + (s + 1) := by ring
    rw [h3] at h1
    rw [max_lt_iff]
    constructor
    · exact lt_of_lt_of_le (by omega) (le_max_left _ _)
    · exact lt_of_lt_of_le (by omega) (le_max_left _ _)

theorem aux_sdp_L_nodup (k s j : ℕ) (hs : 1 ≤ s) (hj1 : 1 ≤ j) : (aux_sdp_L k s j).Nodup :=
  (aux_sdp_L_pairwise k s j hs hj1).imp (fun h => ne_of_lt h)

theorem aux_sdp_L_length (k s j : ℕ) (hk : 2 ≤ k) : (aux_sdp_L k s j).length = k := by
  unfold aux_sdp_L
  simp
  omega

theorem aux_sdp_sort_L (k s j : ℕ) (hs : 1 ≤ s) (hj1 : 1 ≤ j) :
    (aux_sdp_L k s j).toFinset.sort = aux_sdp_L k s j :=
  (List.toFinset_sort (· ≤ ·) (aux_sdp_L_nodup k s j hs hj1)).2
    ((aux_sdp_L_pairwise k s j hs hj1).imp (fun h => le_of_lt h))

theorem aux_sdp_mod_inj (s j j' : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ s + 1) (h1' : 1 ≤ j')
    (h2' : j' ≤ s + 1) (h : j % (s + 1) = j' % (s + 1)) : j = j' := by
  rcases lt_or_eq_of_le h2 with hl | he
  · rcases lt_or_eq_of_le h2' with hl' | he'
    · rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at h
      exact h
    · rw [Nat.mod_eq_of_lt hl, he', Nat.mod_self] at h
      omega
  · rcases lt_or_eq_of_le h2' with hl' | he'
    · rw [Nat.mod_eq_of_lt hl', he, Nat.mod_self] at h
      omega
    · omega

/-- Members of the shadow set for class `j` are congruent to `j` modulo `s + 1`. -/
theorem aux_sdp_B_mod (k s j x : ℕ) (hs : 1 ≤ s) (hj1 : 1 ≤ j)
    (hx : x ∈ ((aux_sdp_L k s j).toFinset).erase (if j = 1 then 2 else 1)) :
    x % (s + 1) = j % (s + 1) := by
  rw [Finset.mem_erase, List.mem_toFinset] at hx
  obtain ⟨hne, hmem⟩ := hx
  unfold aux_sdp_L at hmem
  rw [List.mem_cons] at hmem
  rcases hmem with h | h
  · subst h
    by_cases hj : j = 1
    · subst hj; rfl
    · simp [hj] at hne
  · simp only [List.mem_map, List.mem_range] at h
    obtain ⟨t, _, rfl⟩ := h
    by_cases hj : j = 1
    · subst hj
      simp only [if_true] at hne
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht; simp at hne
      · have h4 : 1 * (s + 1) ≤ t * (s + 1) := Nat.mul_le_mul_right _ ht
        rw [max_eq_left (by omega)]
        exact Nat.add_mul_mod_self_right _ _ _
    · rw [max_eq_left (by omega)]
      exact Nat.add_mul_mod_self_right _ _ _

theorem aux_sdp_j_mem (k s j : ℕ) (hk : 2 ≤ k) (hj1 : 1 ≤ j) :
    j ∈ ((aux_sdp_L k s j).toFinset).erase (if j = 1 then 2 else 1) := by
  rw [Finset.mem_erase, List.mem_toFinset]
  unfold aux_sdp_L
  by_cases hj : j = 1
  · subst hj; simp
  · refine ⟨by simp [hj], ?_⟩
    rw [List.mem_cons]
    right
    simp only [List.mem_map, List.mem_range]
    exact ⟨0, by omega, by simp; omega⟩

theorem aux_sdp_y_mem (k s j : ℕ) (hk : 2 ≤ k) :
    (if j = 1 then 2 else 1) ∈ (aux_sdp_L k s j).toFinset := by
  rw [List.mem_toFinset]
  unfold aux_sdp_L
  by_cases hj : j = 1
  · subst hj
    simp only [if_true, List.mem_cons, List.mem_map, List.mem_range]
    right
    exact ⟨0, by omega, by simp⟩
  · simp [hj]

end FranklKupavskii2022.EMC

open FranklKupavskii2022.EMC
open FinsetFamily

theorem solution (m k s : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard k) (hinit : IsInitial m k G)
    (hν : matchingNumber (∂ G) ≤ s) :
    ∀ F ∈ G, ∃ i, 1 ≤ i ∧ i < k ∧ i + 1 ≤ (F ∩ Finset.Icc 1 (i * (s + 1) - 1)).card := by
  intro F hFG
  by_contra hcon
  push Not at hcon
  have hFm := hG hFG
  rw [Finset.mem_powersetCard] at hFm
  obtain ⟨hFsub, hFcard⟩ := hFm
  have hlen : F.sort.length = k := by rw [Finset.length_sort, hFcard]
  have hF1 : ∀ x ∈ F, 1 ≤ x := fun x hx => (Finset.mem_Icc.1 (hFsub hx)).1
  have hFm' : ∀ x ∈ F, x ≤ m := fun x hx => (Finset.mem_Icc.1 (hFsub hx)).2
  have hFget : ∀ i (hi : i < F.sort.length), F.sort.get ⟨i, hi⟩ ∈ F := by
    intro i hi
    rw [← Finset.mem_sort (s := F) (r := fun a b => a ≤ b)]
    exact List.get_mem _ _
  have hbound : ∀ i (hi : i < F.sort.length), i * (s + 1) ≤ F.sort.get ⟨i, hi⟩ := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp
    by_contra hlt
    push Not at hlt
    have h1 := aux_sdp_card F hF1 (i * (s + 1) - 1) i hi (by omega)
    have h2 := hcon i hpos (by omega)
    omega
  -- each explicit k-set belongs to G
  have hHG : ∀ j, 1 ≤ j → j ≤ s + 1 → (aux_sdp_L k s j).toFinset ∈ G := by
    intro j hj1 hj2
    have hcmp : ∀ i (h1 : i < (aux_sdp_L k s j).length) (h2 : i < F.sort.length),
        (aux_sdp_L k s j).get ⟨i, h1⟩ ≤ F.sort.get ⟨i, h2⟩ := by
      intro i h1 h2
      rcases i with _ | t
      · have := hF1 _ (hFget 0 h2)
        simpa [aux_sdp_L] using this
      · have hb := hbound (t + 1) h2
        have h3 : (t + 1) * (s + 1) = t * (s + 1) + (s + 1) := by ring
        rw [h3] at hb
        have h4 : (aux_sdp_L k s j).get ⟨t + 1, h1⟩ = max (j + t * (s + 1)) 2 := by
          simp [aux_sdp_L]
        rw [h4, max_le_iff]
        constructor <;> omega
    have hlenL := aux_sdp_L_length k s j hk
    have hsub : (aux_sdp_L k s j).toFinset ⊆ Finset.Icc 1 m := by
      intro x hx
      rw [List.mem_toFinset] at hx
      obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_iff_get.1 hx
      have hi2 : i < F.sort.length := by omega
      have hc := hcmp i hi hi2
      have hm := hFm' _ (hFget i hi2)
      rw [Finset.mem_Icc]
      refine ⟨?_, le_trans hc hm⟩
      rcases i with _ | t
      · simp [aux_sdp_L]
      · have h4 : (aux_sdp_L k s j).get ⟨t + 1, hi⟩ = max (j + t * (s + 1)) 2 := by
          simp [aux_sdp_L]
        rw [h4]
        exact le_trans (by norm_num) (le_max_right _ _)
    have hcard : (aux_sdp_L k s j).toFinset.card = k := by
      rw [List.toFinset_card_of_nodup (aux_sdp_L_nodup k s j hs hj1), hlenL]
    have hF2 : List.Forall₂ (· ≤ ·) (aux_sdp_L k s j).toFinset.sort F.sort := by
      rw [aux_sdp_sort_L k s j hs hj1, List.forall₂_iff_get]
      exact ⟨by rw [hlenL, hlen], hcmp⟩
    by_cases heq : (aux_sdp_L k s j).toFinset = F
    · rw [heq]; exact hFG
    · exact hinit _ (Finset.mem_powersetCard.2 ⟨hsub, hcard⟩) F hFG ⟨hF2, heq⟩
  -- the matching
  set B : ℕ → Finset ℕ := fun j => ((aux_sdp_L k s j).toFinset).erase (if j = 1 then 2 else 1)
    with hBdef
  set M : Finset (Finset ℕ) := (Finset.Icc 1 (s + 1)).image B with hMdef
  have hMsub : M ⊆ ∂ G := by
    intro A hA
    rw [hMdef, Finset.mem_image] at hA
    obtain ⟨j, hj, rfl⟩ := hA
    rw [Finset.mem_Icc] at hj
    exact Finset.erase_mem_shadow (hHG j hj.1 hj.2) (aux_sdp_y_mem k s j hk)
  have hMdisj : ∀ A ∈ M, ∀ A' ∈ M, A ≠ A' → Disjoint A A' := by
    intro A hA A' hA' hne
    rw [hMdef, Finset.mem_image] at hA hA'
    obtain ⟨j, hj, rfl⟩ := hA
    obtain ⟨j', hj', rfl⟩ := hA'
    rw [Finset.mem_Icc] at hj hj'
    have hjj : j ≠ j' := by
      intro h; subst h; exact hne rfl
    rw [Finset.disjoint_left]
    intro x hx hx'
    have e1 := aux_sdp_B_mod k s j x hs hj.1 hx
    have e2 := aux_sdp_B_mod k s j' x hs hj'.1 hx'
    exact hjj (aux_sdp_mod_inj s j j' hj.1 hj.2 hj'.1 hj'.2 (e1.symm.trans e2))
  have hMcard : M.card = s + 1 := by
    rw [hMdef, Finset.card_image_of_injOn]
    · simp
    · intro j hj j' hj' hB
      simp only [Finset.coe_Icc, Set.mem_Icc] at hj hj'
      have hmem := aux_sdp_j_mem k s j hk hj.1
      have hmem' : j ∈ B j' := by
        have : B j = B j' := hB
        rw [← this]; exact hmem
      have e := aux_sdp_B_mod k s j' j hs hj'.1 hmem'
      exact aux_sdp_mod_inj s j j' hj.1 hj.2 hj'.1 hj'.2 e
  have hle : M.card ≤ matchingNumber (∂ G) := by
    unfold matchingNumber
    exact Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hMsub, hMdisj⟩)
  omega
