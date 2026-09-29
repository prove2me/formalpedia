-- Prove2me | solution 1 for CompetitivePaging.Marking.adversary_cost_ge_clean_sub_d
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:54:01.408577+00:00
-- url     : https://prove2.me/submissions/cce2b237-4ad1-4d1b-99fb-b54d907ddf84

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

theorem aux_acs_claim {k : ℕ} {M : Type*} (σ : List M) (S : ℕ → KServer.Config k M)
    (hlazy : IsLazySchedule σ S) (v : M) (i : ℕ) (h0 : ∀ j, S i j ≠ v) :
    ∀ m, i ≤ m → m ≤ σ.length → (∃ j, S m j = v) →
      ∃ s : Fin σ.length, i ≤ s.val ∧ s.val < m ∧ σ.get s = v ∧ ∀ j, S s j ≠ σ.get s := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _ ⟨j, hj⟩
    exact absurd hj (h0 j)
  | succ m hm ih =>
    intro hlen ⟨j, hj⟩
    by_cases hP : ∃ j, S m j = v
    · obtain ⟨s, hs1, hs2, hs3, hs4⟩ := ih (by omega) hP
      exact ⟨s, hs1, by omega, hs3, hs4⟩
    · have hml : m < σ.length := by omega
      obtain ⟨h1, h2⟩ := hlazy ⟨m, hml⟩
      by_cases hc : ∃ j, S m j = σ.get ⟨m, hml⟩
      · have := h1 hc
        simp only at this
        rw [this] at hj
        exact absurd ⟨j, hj⟩ hP
      · obtain ⟨j0, hj0⟩ := h2 hc
        simp only at hj0
        rw [hj0] at hj
        by_cases hjj : j = j0
        · subst hjj
          rw [Function.update_self] at hj
          refine ⟨⟨m, hml⟩, hm, by simp, hj, ?_⟩
          intro j' hj'
          exact hc ⟨j', hj'⟩
        · rw [Function.update_of_ne hjj] at hj
          exact absurd ⟨j, hj⟩ hP

end CompetitivePaging.Marking

open CompetitivePaging.Marking

theorem solution {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k) (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
        - ((Finset.univ.filter
            (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ)
      ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) := by
  classical
  set Mk := marksAt k (initVertices e hkn) σ i with hMk
  set C := phaseRequested σ i i' \ Mk with hC
  set D := Finset.univ.filter (fun j : Fin k => S i j ∉ Mk) with hD
  set T := Finset.univ.filter
    (fun s : Fin σ.length => i ≤ s.val ∧ s.val < i' ∧ ∀ j, S s j ≠ σ.get s) with hT
  have hsub : C ⊆ D.image (S i) ∪ T.image σ.get := by
    intro v hv
    rw [hC, Finset.mem_sdiff] at hv
    obtain ⟨hvP, hvM⟩ := hv
    by_cases h : ∃ j, S i j = v
    · obtain ⟨j, hj⟩ := h
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      refine ⟨j, ?_, hj⟩
      rw [hD, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hj ▸ hvM⟩
    · push Not at h
      apply Finset.mem_union_right
      unfold phaseRequested at hvP
      rw [List.mem_toFinset, List.mem_iff_getElem] at hvP
      obtain ⟨p, hp, hpv⟩ := hvP
      simp only [List.length_take, List.length_drop] at hp
      rw [List.getElem_take, List.getElem_drop] at hpv
      have htl : i + p < σ.length := by omega
      have hti : i + p < i' := by omega
      set t := i + p with ht
      have hserve : ∃ j, S (t + 1) j = v := by
        obtain ⟨h1, h2⟩ := hlazy ⟨t, htl⟩
        by_cases hc : ∃ j, S t j = σ.get ⟨t, htl⟩
        · have := h1 hc
          simp only at this
          obtain ⟨j, hj⟩ := hc
          refine ⟨j, ?_⟩
          rw [this, hj, ← hpv]
          rfl
        · obtain ⟨j0, hj0⟩ := h2 hc
          simp only at hj0
          refine ⟨j0, ?_⟩
          rw [hj0, Function.update_self, ← hpv]
          rfl
      obtain ⟨s, hs1, hs2, hs3, hs4⟩ :=
        aux_acs_claim σ S hlazy v i h (t + 1) (by omega) (by omega) hserve
      rw [Finset.mem_image]
      refine ⟨s, ?_, hs3⟩
      rw [hT, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hs1, by omega, hs4⟩
  have hcard : (C.card : ℝ) ≤ D.card + T.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (D.image (S i)) (T.image σ.get)
    have h3 := Finset.card_image_le (s := D) (f := S i)
    have h4 := Finset.card_image_le (s := T) (f := σ.get)
    exact_mod_cast (by omega : C.card ≤ D.card + T.card)
  have hnonneg : ∀ t, 0 ≤ KServer.moveCost (S t) (S (t + 1)) := by
    intro t
    unfold KServer.moveCost
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  have hone : ∀ s ∈ T, (1 : ℝ) ≤ KServer.moveCost (S s) (S (s + 1)) := by
    intro s hs
    rw [hT, Finset.mem_filter] at hs
    obtain ⟨_, _, _, hs4⟩ := hs
    obtain ⟨_, h2⟩ := hlazy s
    have hc : ¬ ∃ j, S s j = σ.get s := by
      rintro ⟨j, hj⟩
      exact hs4 j hj
    obtain ⟨j0, hj0⟩ := h2 hc
    unfold KServer.moveCost
    have hle := Finset.single_le_sum (f := fun j => dist (S s j) (S (s + 1) j))
      (fun _ _ => dist_nonneg) (Finset.mem_univ j0)
    rw [hj0, Function.update_self, hdist _ _ (hs4 j0)] at hle
    rw [hj0]
    exact hle
  have hTsum : (T.card : ℝ) ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) := by
    calc (T.card : ℝ) = ∑ s ∈ T, (1 : ℝ) := by simp
      _ ≤ ∑ s ∈ T, KServer.moveCost (S s) (S (s + 1)) := Finset.sum_le_sum hone
      _ = ∑ t ∈ T.map Fin.valEmbedding, KServer.moveCost (S t) (S (t + 1)) := by
        rw [Finset.sum_map]
        rfl
      _ ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          rw [Finset.mem_map] at ht
          obtain ⟨s, hs, rfl⟩ := ht
          rw [hT, Finset.mem_filter] at hs
          rw [Finset.mem_Ico]
          exact ⟨hs.2.1, hs.2.2.1⟩
        · intro t _ _
          exact hnonneg t
  linarith
