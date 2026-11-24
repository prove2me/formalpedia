-- Prove2me | solution 1 for CharonChurn.Main.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:08:26.089206+00:00
-- url     : https://prove2.me/submissions/b24b0626-448a-4e1f-9045-ab8bd45be78f

import Mathlib
import Definitions.Def_CharonChurn_Main_Connectivity

namespace CharonChurn.Main

theorem conn_of_core_aux {α : Type*} (G : SimpleGraph α) (s t : Set α) (hts : t ⊆ s)
    (ht : (G.induce t).Connected) (hadj : ∀ x ∈ s, x ∉ t → ∃ y ∈ t, G.Adj x y) :
    (G.induce s).Connected := by
  have hmap : ∀ a b : t, (G.induce s).Reachable ⟨a, hts a.2⟩ ⟨b, hts b.2⟩ := fun a b =>
    (ht.preconnected a b).map (G.induceHomOfLE hts).toHom
  have hto : ∀ x : s, ∃ y : t, (G.induce s).Reachable x ⟨y, hts y.2⟩ := by
    intro x
    by_cases hx : (x : α) ∈ t
    · exact ⟨⟨x, hx⟩, by rfl⟩
    · obtain ⟨y, hy, hxy⟩ := hadj x x.2 hx
      refine ⟨⟨y, hy⟩, SimpleGraph.Adj.reachable ?_⟩
      exact hxy
  rw [SimpleGraph.connected_iff]
  refine ⟨fun x y => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hto x
    obtain ⟨b, hb⟩ := hto y
    exact (ha.trans (hmap a b)).trans hb.symm
  · obtain ⟨a⟩ := ht.nonempty
    exact ⟨⟨a, hts a.2⟩⟩

theorem lt_kappa_iff {α : Type*} [DecidableEq α] (G : SimpleGraph α) (S : Finset α) (h : ℕ) :
    h < kappa G S ↔ ∀ Z ⊆ S, Z.card ≤ h → ¬ IsSeparating G S Z := by
  classical
  unfold kappa
  rw [Nat.lt_find_iff]
  constructor
  · intro H Z hZ hc hsep
    exact H Z.card hc ⟨Z, hZ, rfl, hsep⟩
  · rintro H m hm ⟨Z, hZ, rfl, hsep⟩
    exact H Z hZ hm hsep

end CharonChurn.Main

open CharonChurn.Main

theorem solution {α : Type*} [DecidableEq α] (Q : SimpleGraph α) (S K : Finset α) (hK : K ⊆ S)
    (h : ℕ) (hcore : h < kappa Q K) (hattach : ∀ v ∈ S \ K, h < (nbrsIn Q K v).card) :
    h < kappa Q S := by
  classical
  rw [lt_kappa_iff] at hcore ⊢
  intro Z hZS hZc hsep
  have hZK : Z ∩ K ⊆ K := Finset.inter_subset_right
  have hc' : (Z ∩ K).card ≤ h := (Finset.card_le_card Finset.inter_subset_left).trans hZc
  have hcore' := hcore (Z ∩ K) hZK hc'
  unfold IsSeparating at hcore' hsep
  push Not at hcore'
  obtain ⟨hconn, hcard⟩ := hcore'
  have heq : K \ (Z ∩ K) = K \ Z := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [heq] at hconn hcard
  have hsub : K \ Z ⊆ S \ Z := Finset.sdiff_subset_sdiff hK (le_refl _)
  rcases hsep with hsep | hsep
  · apply hsep
    apply conn_of_core_aux Q _ _ (by exact_mod_cast hsub) hconn
    intro x hx hxt
    have hx' : x ∈ S \ Z := by exact_mod_cast hx
    have hxt' : x ∉ K \ Z := by exact_mod_cast hxt
    have hxK : x ∉ K := by
      intro hxK
      exact hxt' (Finset.mem_sdiff.mpr ⟨hxK, (Finset.mem_sdiff.mp hx').2⟩)
    have hbig := hattach x (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx').1, hxK⟩)
    -- some neighbour in K avoids Z
    by_contra hno
    push Not at hno
    have hsubZ : nbrsIn Q K x ⊆ Z := by
      intro y hy
      unfold nbrsIn at hy
      rw [Finset.mem_filter] at hy
      by_contra hyZ
      exact hno y (by simp [hy.1, hyZ]) hy.2
    have := Finset.card_le_card hsubZ
    omega
  · have := Finset.card_le_card hsub
    omega
