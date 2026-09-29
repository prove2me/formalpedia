-- Prove2me | solution 1 for CompetitivePaging.Marking.adversary_phase_cost_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:05:01.84891+00:00
-- url     : https://prove2.me/submissions/b8bc1058-8e3f-4153-8007-d797bfb4ecb8

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm



namespace CompetitivePaging.Marking

theorem mk_mem_phaseRequested {M : Type*} [DecidableEq M] (σ : List M) (i t : ℕ) (x : M) :
    x ∈ phaseRequested σ i t ↔
      ∃ u, ∃ hu : u < σ.length, i ≤ u ∧ u < t ∧ σ.get ⟨u, hu⟩ = x := by
  unfold phaseRequested
  rw [List.mem_toFinset, List.mem_iff_getElem]
  constructor
  · rintro ⟨n, hn, rfl⟩
    simp only [List.length_take, List.length_drop] at hn
    refine ⟨i + n, by omega, by omega, by omega, ?_⟩
    simp [List.getElem_take, List.getElem_drop]
  · rintro ⟨u, hu, h1, h2, rfl⟩
    refine ⟨u - i, ?_, ?_⟩
    · simp only [List.length_take, List.length_drop]; omega
    · simp only [List.getElem_take, List.getElem_drop, List.get_eq_getElem]
      congr 1; omega

theorem mk_phaseRequested_succ {M : Type*} [DecidableEq M] (σ : List M) (i t : ℕ)
    (hit : i ≤ t) (ht : t < σ.length) :
    phaseRequested σ i (t + 1) = insert (σ.get ⟨t, ht⟩) (phaseRequested σ i t) := by
  ext x
  rw [Finset.mem_insert, mk_mem_phaseRequested, mk_mem_phaseRequested]
  constructor
  · rintro ⟨u, hu, h1, h2, rfl⟩
    by_cases hut : u = t
    · subst hut; left; rfl
    · right; exact ⟨u, hu, h1, by omega, rfl⟩
  · rintro (rfl | ⟨u, hu, h1, h2, rfl⟩)
    · exact ⟨t, ht, hit, by omega, rfl⟩
    · exact ⟨u, hu, h1, by omega, rfl⟩

theorem mk_phaseRequested_self {M : Type*} [DecidableEq M] (σ : List M) (i : ℕ) :
    phaseRequested σ i i = ∅ := by
  unfold phaseRequested; simp

theorem mk_phaseRequested_mono {M : Type*} [DecidableEq M] (σ : List M) (a b c d : ℕ)
    (h1 : a ≤ c) (h2 : d ≤ b) : phaseRequested σ c d ⊆ phaseRequested σ a b := by
  intro x hx
  rw [mk_mem_phaseRequested] at hx ⊢
  obtain ⟨u, hu, h3, h4, rfl⟩ := hx
  exact ⟨u, hu, by omega, by omega, rfl⟩

theorem mk_marksAt_succ {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (σ : List M)
    (t : ℕ) (ht : t < σ.length) :
    marksAt k V σ (t + 1) = marksAfter k (marksAt k V σ t) (σ.get ⟨t, ht⟩) := by
  unfold marksAt
  rw [List.take_succ, List.foldl_append, List.getElem?_eq_getElem ht]
  simp

theorem mk_marksAt_phase {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (σ : List M)
    (i i' : ℕ) (hphase : IsCompletePhase k V σ i i') :
    ∀ t, i + 1 ≤ t → t ≤ i' → marksAt k V σ t = phaseRequested σ i t := by
  obtain ⟨⟨hi, hic⟩, ⟨hi', _⟩, hii', hno⟩ := hphase
  intro t h1 h2
  induction t, h1 using Nat.le_induction with
  | base =>
    rw [mk_marksAt_succ k V σ i hi, mk_phaseRequested_succ σ i i le_rfl hi,
      mk_phaseRequested_self]
    unfold marksAfter; rw [if_pos hic]; rfl
  | succ t ht ih =>
    have htl : t < σ.length := by omega
    rw [mk_marksAt_succ k V σ t htl, mk_phaseRequested_succ σ i t (by omega) htl,
      ← ih (by omega)]
    unfold marksAfter
    rw [if_neg]
    intro hc
    exact hno t (by omega) (by omega) ⟨htl, hc⟩

section lazy
variable {k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]

theorem mk_lazy_pos (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S)
    (t : ℕ) (ht : t < σ.length) (j : Fin k) :
    S (t + 1) j = S t j ∨ S (t + 1) j = σ.get ⟨t, ht⟩ := by
  have h := hlazy ⟨t, ht⟩
  simp only at h
  by_cases hc : ∃ i, S t i = σ.get ⟨t, ht⟩
  · left; rw [h.1 hc]
  · obtain ⟨i, hi⟩ := h.2 hc
    rw [hi]
    by_cases hij : j = i
    · subst hij; right; simp
    · left; simp [Function.update_of_ne hij]

theorem mk_lazy_cov (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S)
    (t : ℕ) (ht : t < σ.length) (hc : ∃ i, S t i = σ.get ⟨t, ht⟩) : S (t + 1) = S t :=
  (hlazy ⟨t, ht⟩).1 hc

theorem mk_moveCost_nonneg (C C' : KServer.Config k M) : 0 ≤ KServer.moveCost C C' := by
  unfold KServer.moveCost
  exact Finset.sum_nonneg (fun _ _ => dist_nonneg)

theorem mk_lazy_uncov (hdist : ∀ x y : M, x ≠ y → dist x y = 1)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S)
    (t : ℕ) (ht : t < σ.length) (hc : ¬ ∃ i, S t i = σ.get ⟨t, ht⟩) :
    1 ≤ KServer.moveCost (S t) (S (t + 1)) := by
  obtain ⟨i, hi⟩ := (hlazy ⟨t, ht⟩).2 hc
  simp only at hi
  unfold KServer.moveCost
  have hne : S t i ≠ σ.get ⟨t, ht⟩ := fun h => hc ⟨i, h⟩
  have : dist (S t i) (S (t + 1) i) = 1 := by
    rw [hi]; simp only [Function.update_self]; exact hdist _ _ hne
  rw [← this]
  exact Finset.single_le_sum (f := fun j => dist (S t j) (S (t + 1) j))
    (fun _ _ => dist_nonneg) (Finset.mem_univ i)

theorem mk_pos_inv (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S)
    (a : ℕ) : ∀ t, a ≤ t → t ≤ σ.length → ∀ j,
      S t j = S a j ∨ S t j ∈ phaseRequested σ a t := by
  intro t h1 h2
  induction t, h1 using Nat.le_induction with
  | base => intro j; left; rfl
  | succ t ht ih =>
    intro j
    have htl : t < σ.length := by omega
    rw [mk_phaseRequested_succ σ a t ht htl]
    rcases mk_lazy_pos σ S hlazy t htl j with h | h
    · rw [h]
      rcases ih (by omega) j with h' | h'
      · left; exact h'
      · right; exact Finset.mem_insert_of_mem h'
    · right; rw [h]; exact Finset.mem_insert_self _ _

theorem mk_cost_step (hdist : ∀ x y : M, x ≠ y → dist x y = 1)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i t : ℕ)
    (hit : i ≤ t) :
    ∑ u ∈ Finset.Ico i (t + 1), KServer.moveCost (S u) (S (u + 1)) =
      ∑ u ∈ Finset.Ico i t, KServer.moveCost (S u) (S (u + 1))
        + KServer.moveCost (S t) (S (t + 1)) := by
  rw [Finset.sum_Ico_succ_top hit]

/-- clean vertices not initially covered cost a move each. -/
theorem mk_clean_inv (hdist : ∀ x y : M, x ≠ y → dist x y = 1)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i : ℕ) :
    ∀ t, i ≤ t → t ≤ σ.length →
      (((phaseRequested σ i t) \ (Finset.univ.image (S i))).card : ℝ) ≤
        ∑ u ∈ Finset.Ico i t, KServer.moveCost (S u) (S (u + 1)) := by
  intro t h1 h2
  induction t, h1 using Nat.le_induction with
  | base => simp [mk_phaseRequested_self]
  | succ t ht ih =>
    have htl : t < σ.length := by omega
    rw [mk_cost_step hdist σ S hlazy i t ht, mk_phaseRequested_succ σ i t ht htl]
    have ih' := ih (by omega)
    by_cases hc : ∃ j, S t j = σ.get ⟨t, htl⟩
    · have hmem : σ.get ⟨t, htl⟩ ∈ Finset.univ.image (S i) ∪ phaseRequested σ i t := by
        obtain ⟨j, hj⟩ := hc
        rcases mk_pos_inv σ S hlazy i t ht (by omega) j with h | h
        · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_univ _, by rw [← h, hj]⟩)
        · exact Finset.mem_union_right _ (hj ▸ h)
      have : insert (σ.get ⟨t, htl⟩) (phaseRequested σ i t) \ Finset.univ.image (S i) =
          phaseRequested σ i t \ Finset.univ.image (S i) := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | h, h'⟩
          · rcases Finset.mem_union.1 hmem with h | h
            · exact absurd h h'
            · exact ⟨h, h'⟩
          · exact ⟨h, h'⟩
        · rintro ⟨h, h'⟩; exact ⟨Or.inr h, h'⟩
      rw [this]
      have := mk_moveCost_nonneg (S t) (S (t + 1))
      linarith
    · have h1 := mk_lazy_uncov hdist σ S hlazy t htl hc
      have h3 : insert (σ.get ⟨t, htl⟩) (phaseRequested σ i t) \ Finset.univ.image (S i) ⊆
          insert (σ.get ⟨t, htl⟩) (phaseRequested σ i t \ Finset.univ.image (S i)) := by
        intro x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        tauto
      have h4 := (Finset.card_le_card h3).trans (Finset.card_insert_le _ _)
      have h5 : ((insert (σ.get ⟨t, htl⟩) (phaseRequested σ i t) \
          Finset.univ.image (S i)).card : ℝ) ≤
          ((phaseRequested σ i t \ Finset.univ.image (S i)).card : ℝ) + 1 := by
        exact_mod_cast h4
      linarith

theorem mk_clean_sub_d (hdist : ∀ x y : M, x ≠ y → dist x y = 1)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hi' : i ≤ i') (hl : i' ≤ σ.length) (M0 : Finset M) :
    ((phaseRequested σ i i' \ M0).card : ℝ)
        - ((Finset.univ.filter (fun j : Fin k => S i j ∉ M0)).card : ℝ)
      ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) := by
  have h1 := mk_clean_inv hdist σ S hlazy i i' hi' hl
  have hsub : phaseRequested σ i i' \ M0 ⊆
      (phaseRequested σ i i' \ Finset.univ.image (S i)) ∪
        (Finset.univ.filter (fun j : Fin k => S i j ∉ M0)).image (S i) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hxi : x ∈ Finset.univ.image (S i)
    · apply Finset.mem_union_right
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hxi
      exact Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx.2⟩, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx.1, hxi⟩)
  have h2 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h3 := Finset.card_image_le (s := Finset.univ.filter (fun j : Fin k => S i j ∉ M0))
    (f := S i)
  have h4 : ((phaseRequested σ i i' \ M0).card : ℝ) ≤
      ((phaseRequested σ i i' \ Finset.univ.image (S i)).card : ℝ) +
        ((Finset.univ.filter (fun j : Fin k => S i j ∉ M0)).card : ℝ) := by
    exact_mod_cast h2.trans (Nat.add_le_add_left h3 _)
  linarith

theorem mk_clean_core {n : ℕ} (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1)
    (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
        - ((Finset.univ.filter
            (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ)
      ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) := by
  obtain ⟨_, ⟨hi', _⟩, hii', _⟩ := hphase
  exact mk_clean_sub_d hdist σ S hlazy i i' hii'.le hi'.le _

theorem mk_dend_core {n : ℕ} (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1)
    (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    ((Finset.univ.filter
        (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)
      ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) := by
  set V := initVertices e hkn
  have hP := mk_marksAt_phase k V σ i i' hphase i' (by have := hphase.2.2.1; omega) le_rfl
  obtain ⟨_, ⟨hi', hic'⟩, hii', _⟩ := hphase
  set P := marksAt k V σ i'
  set J := Finset.univ.filter (fun j : Fin k => S i' j ∈ P)
  -- invariant
  have inv : ∀ t, i ≤ t → t ≤ i' →
      ((J.image (S i) ∪ phaseRequested σ i t).card : ℝ) ≤
        (J.card : ℝ) + ∑ u ∈ Finset.Ico i t, KServer.moveCost (S u) (S (u + 1)) := by
    intro t h1 h2
    induction t, h1 using Nat.le_induction with
    | base =>
      simp only [mk_phaseRequested_self, Finset.union_empty, Finset.Ico_self, Finset.sum_empty,
        add_zero]
      exact_mod_cast Finset.card_image_le
    | succ t ht ih =>
      have htl : t < σ.length := by omega
      rw [mk_cost_step hdist σ S hlazy i t ht, mk_phaseRequested_succ σ i t ht htl]
      have ih' := ih (by omega)
      by_cases hc : ∃ j, S t j = σ.get ⟨t, htl⟩
      · have hmem : σ.get ⟨t, htl⟩ ∈ J.image (S i) ∪ phaseRequested σ i t := by
          obtain ⟨j, hj⟩ := hc
          rcases mk_pos_inv σ S hlazy i t ht (by omega) j with h | h
          · by_cases hjJ : j ∈ J
            · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, hjJ, by rw [← h, hj]⟩)
            · exfalso
              have hjP : S i' j ∉ P := by
                intro hh; exact hjJ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hh⟩)
              have hσP : σ.get ⟨t, htl⟩ ∈ P := by
                rw [hP, mk_mem_phaseRequested]; exact ⟨t, htl, ht, by omega, rfl⟩
              rcases mk_pos_inv σ S hlazy t i' (by omega) hi'.le j with h' | h'
              · exact hjP (h' ▸ hj ▸ hσP)
              · exact hjP (hP ▸ mk_phaseRequested_mono σ i i' t i' ht le_rfl h')
          · exact Finset.mem_union_right _ (hj ▸ h)
        rw [Finset.union_insert, Finset.insert_eq_of_mem hmem]
        have := mk_moveCost_nonneg (S t) (S (t + 1))
        linarith
      · have h1 := mk_lazy_uncov hdist σ S hlazy t htl hc
        rw [Finset.union_insert]
        have h4 := Finset.card_insert_le (σ.get ⟨t, htl⟩) (J.image (S i) ∪ phaseRequested σ i t)
        have h5 : ((insert (σ.get ⟨t, htl⟩) (J.image (S i) ∪ phaseRequested σ i t)).card : ℝ)
            ≤ ((J.image (S i) ∪ phaseRequested σ i t).card : ℝ) + 1 := by exact_mod_cast h4
        linarith
  have hfin := inv i' hii'.le le_rfl
  rw [← hP] at hfin
  have hPk : k ≤ P.card := by
    have := Finset.card_insert_le (σ.get ⟨i', hi'⟩) P
    omega
  have hPU : (P.card : ℝ) ≤ ((J.image (S i) ∪ P).card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.subset_union_right
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (fun j => S i' j ∈ P)
  simp only [Finset.card_univ, Fintype.card_fin] at hsplit
  have hs' : ((Finset.univ.filter (fun j : Fin k => S i' j ∉ P)).card : ℝ) + (J.card : ℝ)
      = (k : ℝ) := by
    have h' : (Finset.univ.filter (fun j : Fin k => S i' j ∉ P)).card +
        (Finset.univ.filter (fun j : Fin k => S i' j ∈ P)).card = k := by
      rw [add_comm, Finset.card_filter_add_card_filter_not]; simp
    exact_mod_cast h'
  have hPk' : (k : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hPk
  linarith

theorem mk_half_core {n : ℕ} (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1)
    (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    max (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)
        ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) ∧
      (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ)
          + ((Finset.univ.filter
              (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)) / 2
        ≤ max (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ) := by
  refine ⟨max_le (mk_clean_core e hdist hkn σ S hlazy i i' hphase)
    (mk_dend_core e hdist hkn σ S hlazy i i' hphase), ?_⟩
  have := le_max_left (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)
  have := le_max_right (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)
  linarith

end lazy

end CompetitivePaging.Marking

open CompetitivePaging.Marking


theorem solution {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k) (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    max (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)
        ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) ∧
      (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ)
          + ((Finset.univ.filter
              (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)) / 2
        ≤ max (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ) := by
  exact mk_half_core e hdist hkn σ S hlazy i i' hphase
