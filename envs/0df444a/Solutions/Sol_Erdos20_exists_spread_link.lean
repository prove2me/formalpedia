-- Prove2me | solution 1 for Erdos20.exists_spread_link
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-09-26T15:54:41.228825+00:00
-- url     : https://prove2.me/submissions/4fb3c8de-23b5-4b63-a700-0fbd3b33fa7a

import Definitions.Def_SunflowerSpread
import Mathlib.Data.Finset.Max

set_option autoImplicit false

namespace Erdos20

private lemma card_link_eq {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S : Finset α) :
    (link F S).card = (F.filter (fun A => S ⊆ A)).card := by
  apply Finset.card_image_of_injOn
  intro A hA B hB h
  exact Finset.superset_injOn_sdiff S
    (Finset.mem_filter.mp hA).2 (Finset.mem_filter.mp hB).2 h

private lemma card_filter_link_eq {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S T : Finset α) (hd : Disjoint S T) :
    ((link F S).filter (fun A => T ⊆ A)).card =
      (F.filter (fun A => S ∪ T ⊆ A)).card := by
  rw [link, Finset.filter_image, Finset.filter_filter]
  have hfilter : F.filter (fun A => S ⊆ A ∧ T ⊆ A \ S) =
      F.filter (fun A => S ∪ T ⊆ A) := by
    ext A
    simp [Finset.subset_sdiff, hd.symm, Finset.union_subset_iff]
  rw [hfilter]
  apply Finset.card_image_of_injOn
  intro A hA B hB h
  exact Finset.superset_injOn_sdiff S
    (Finset.subset_union_left.trans (Finset.mem_filter.mp hA).2)
    (Finset.subset_union_left.trans (Finset.mem_filter.mp hB).2) h

/-- Maximizing the weighted number of extensions gives a proper core with
a nonempty spread link. This is the deterministic link-extraction step in
the modern sunflower argument. -/
private theorem spread_link_proof {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (n : ℕ) (R : ℝ) (hR : 1 < R)
    (huni : ∀ A ∈ F, A.card = n) (hsize : R ^ n < (F.card : ℝ)) :
    ∃ S : Finset α, S.card < n ∧ (link F S).Nonempty ∧ IsSpread R (link F S) := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hFpos : 0 < (F.card : ℝ) := lt_trans (pow_pos hRpos n) hsize
  have hFne : F.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hFpos)
  let cores : Finset (Finset α) := F.biUnion Finset.powerset
  have hempty : ∅ ∈ cores := by
    obtain ⟨A, hA⟩ := hFne
    exact Finset.mem_biUnion.mpr ⟨A, hA, Finset.empty_mem_powerset A⟩
  obtain ⟨S, hScore, hmax⟩ := Finset.exists_max_image cores
    (fun S => R ^ S.card * ((F.filter (fun A => S ⊆ A)).card : ℝ))
    ⟨∅, hempty⟩
  obtain ⟨A₀, hA₀, hSA₀⟩ := Finset.mem_biUnion.mp hScore
  have hSA₀ : S ⊆ A₀ := Finset.mem_powerset.mp hSA₀
  have hScard : S.card ≤ n := (Finset.card_le_card hSA₀).trans_eq (huni A₀ hA₀)
  have hFweight : (F.card : ℝ) ≤
      R ^ S.card * ((F.filter (fun A => S ⊆ A)).card : ℝ) := by
    simpa using hmax ∅ hempty
  have hproper : S.card < n := by
    by_contra h
    have heq : S.card = n := le_antisymm hScard (Nat.le_of_not_gt h)
    have hSAeq : ∀ A ∈ F, S ⊆ A → A = S := by
      intro A hA hSA
      exact (Finset.eq_of_subset_of_card_le hSA (by rw [huni A hA, heq])).symm
    have hSF : S ∈ F := by simpa [hSAeq A₀ hA₀ hSA₀] using hA₀
    have hfilter : F.filter (fun A => S ⊆ A) = {S} := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => hSAeq A h.1 h.2, fun h => by subst A; exact ⟨hSF, le_rfl⟩⟩
    rw [hfilter, Finset.card_singleton, Nat.cast_one, mul_one, heq] at hFweight
    exact (not_le_of_gt hsize) hFweight
  refine ⟨S, hproper, ?_, ?_⟩
  · exact ⟨A₀ \ S,
      Finset.mem_image.mpr ⟨A₀, Finset.mem_filter.mpr ⟨hA₀, hSA₀⟩, rfl⟩⟩
  · intro T
    by_cases hT : ((link F S).filter (fun A => T ⊆ A)).Nonempty
    · obtain ⟨B, hB⟩ := hT
      obtain ⟨hBlink, hTB⟩ := Finset.mem_filter.mp hB
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hBlink
      obtain ⟨hAF, hSA⟩ := Finset.mem_filter.mp hA
      have hTA : T ⊆ A := hTB.trans Finset.sdiff_subset
      have hd : Disjoint S T := (Finset.subset_sdiff.mp hTB).2.symm
      have hSTcore : S ∪ T ∈ cores :=
        Finset.mem_biUnion.mpr ⟨A, hAF,
          Finset.mem_powerset.mpr (Finset.union_subset hSA hTA)⟩
      have hw := hmax (S ∪ T) hSTcore
      rw [Finset.card_union_of_disjoint hd, pow_add] at hw
      rw [card_filter_link_eq F S T hd, card_link_eq F S]
      apply (mul_le_mul_iff_right₀ (pow_pos hRpos S.card)).mp
      simpa only [mul_assoc] using hw
    · have hz : ((link F S).filter (fun A => T ⊆ A)).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hT)
      simp [hz]

end Erdos20


theorem solution {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (n : ℕ) (R : ℝ) (hR : 1 < R)
    (huni : ∀ A ∈ F, A.card = n) (hsize : R ^ n < (F.card : ℝ)) :
    ∃ S : Finset α, S.card < n ∧ (Erdos20.link F S).Nonempty ∧
      Erdos20.IsSpread R (Erdos20.link F S) :=
  Erdos20.spread_link_proof F n R hR huni hsize
