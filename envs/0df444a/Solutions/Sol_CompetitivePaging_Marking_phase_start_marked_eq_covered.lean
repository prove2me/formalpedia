-- Prove2me | solution 1 for CompetitivePaging.Marking.phase_start_marked_eq_covered
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:04:55.83679+00:00
-- url     : https://prove2.me/submissions/cac71e28-6be7-46a4-b179-eb5e504ba534

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

theorem aux_pmsm_step {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (s : State M) (r : M)
    (hc : s.covered.card = k) (hsub : s.marked ⊆ s.covered) :
    ∀ s' ∈ (step k s r).support,
      s'.marked = marksAfter k s.marked r ∧ s'.covered.card = k ∧ s'.marked ⊆ s'.covered := by
  intro s' hs'
  have hmk : marksAfter k s.marked r ⊆ insert r s.marked := by
    unfold marksAfter
    split_ifs
    · simp
    · exact Finset.Subset.refl _
  unfold step at hs'
  simp only at hs'
  split_ifs at hs' with h1 h2
  · rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨rfl, hc, ?_⟩
    intro x hx
    have := hmk hx
    rw [Finset.mem_insert] at this
    rcases this with rfl | h
    · exact h1
    · exact hsub h
  · rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨v, hv, rfl⟩ := hs'
    rw [PMF.mem_support_uniformOfFinset_iff, Finset.mem_sdiff] at hv
    refine ⟨rfl, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem hv.1, hc]
      · omega
      · exact fun h => h1 (Finset.mem_of_mem_erase h)
    · intro x hx
      have := hmk hx
      rw [Finset.mem_insert] at this ⊢
      rcases this with rfl | h
      · left; rfl
      · right
        rw [Finset.mem_erase]
        exact ⟨fun hxv => hv.2 (hxv ▸ hx), hsub h⟩
  · exfalso
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h2
    unfold marksAfter at h2
    split_ifs at h2 with h3
    · have hne : s.covered.Nonempty := by
        rw [← Finset.card_pos, hc]; omega
      obtain ⟨x, hx⟩ := hne
      have := h2 hx
      rw [Finset.mem_singleton] at this
      subst this
      exact h1 hx
    · have hcm : s.covered ⊆ s.marked := by
        intro x hx
        have := h2 hx
        rw [Finset.mem_insert] at this
        rcases this with rfl | h
        · exact absurd hx h1
        · exact h
      have heq : s.marked = s.covered := Finset.Subset.antisymm hsub hcm
      apply h3
      rw [heq, Finset.card_insert_of_notMem h1, hc]

theorem aux_pmsm_fold {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (l : List M) :
    ∀ (p : PMF (State M)) (m : Finset M),
      (∀ s ∈ p.support, s.marked = m ∧ s.covered.card = k ∧ s.marked ⊆ s.covered) →
      ∀ s ∈ (l.foldl (fun p r => p.bind (fun s => step k s r)) p).support,
        s.marked = l.foldl (marksAfter k) m ∧ s.covered.card = k ∧ s.marked ⊆ s.covered := by
  induction l with
  | nil => intro p m h; simpa using h
  | cons r l ih =>
    intro p m h
    simp only [List.foldl_cons]
    apply ih
    intro s hs
    rw [PMF.mem_support_bind_iff] at hs
    obtain ⟨a, ha, hs⟩ := hs
    obtain ⟨h1, h2, h3⟩ := h a ha
    have := aux_pmsm_step k hk a r h2 h3 s hs
    rw [h1] at this
    exact this

end CompetitivePaging.Marking

open CompetitivePaging.Marking

theorem solution {n k : ℕ} {M : Type*} [DecidableEq M]
    (e : Fin n ≃ M) (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (t : ℕ) (ht : t < σ.length)
    (hstart : IsPhaseStart k (initVertices e hkn) σ t) :
    ∀ s ∈ (lawAfter k (initVertices e hkn) (σ.take t)).support,
      s.marked = s.covered ∧ σ.get ⟨t, ht⟩ ∉ s.marked := by
  intro s hs
  have hV : (initVertices e hkn).card = k := by
    unfold initVertices
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro i j hij
    unfold initConfig at hij
    exact Fin.castLE_injective hkn (e.injective hij)
  have key := aux_pmsm_fold k hk (σ.take t)
    (PMF.pure ⟨initVertices e hkn, initVertices e hkn⟩) (initVertices e hkn) (by
      intro s hs
      rw [PMF.mem_support_pure_iff] at hs
      subst hs
      exact ⟨rfl, hV, Finset.Subset.refl _⟩) s hs
  obtain ⟨h1, h2, h3⟩ := key
  obtain ⟨ht', hcard⟩ := hstart
  change (insert (σ.get ⟨t, ht⟩)
    ((σ.take t).foldl (marksAfter k) (initVertices e hkn))).card = k + 1 at hcard
  rw [← h1] at hcard
  have hle : s.marked.card ≤ k := h2 ▸ Finset.card_le_card h3
  have hnot : σ.get ⟨t, ht⟩ ∉ s.marked := by
    intro hm
    rw [Finset.insert_eq_of_mem hm] at hcard
    omega
  refine ⟨?_, hnot⟩
  rw [Finset.card_insert_of_notMem hnot] at hcard
  exact Finset.eq_of_subset_of_card_le h3 (by omega)
