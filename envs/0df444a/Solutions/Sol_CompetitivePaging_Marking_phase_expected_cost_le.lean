-- Prove2me | solution 1 for CompetitivePaging.Marking.phase_expected_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:40:32.924626+00:00
-- url     : https://prove2.me/submissions/3daef51f-d376-4652-9f1c-72ec59f6fb3b

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

open scoped ENNReal

namespace CompetitivePaging.Marking

theorem aux_pec_marksAfter_subset {M : Type*} [DecidableEq M] (k : ℕ) (mk : Finset M) (r : M) :
    marksAfter k mk r ⊆ insert r mk := by
  unfold marksAfter; split_ifs
  · simp
  · exact le_rfl

theorem aux_pec_step_support {M : Type*} [DecidableEq M] (k : ℕ) (s s' : State M) (r : M)
    (h : s' ∈ (step k s r).support) :
    s'.marked = marksAfter k s.marked r ∧
    ((r ∈ s.covered ∧ s'.covered = s.covered) ∨
     (r ∉ s.covered ∧ ∃ v ∈ s.covered \ marksAfter k s.marked r,
        s'.covered = insert r (s.covered.erase v)) ∨
     (r ∉ s.covered ∧ ¬ (s.covered \ marksAfter k s.marked r).Nonempty ∧
        s'.covered = s.covered)) := by
  unfold step at h
  simp only at h
  split_ifs at h with h1 h2
  · rw [PMF.support_pure, Set.mem_singleton_iff] at h; subst h
    exact ⟨rfl, Or.inl ⟨h1, rfl⟩⟩
  · rw [PMF.support_map, PMF.support_uniformOfFinset] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨rfl, Or.inr (Or.inl ⟨h1, v, hv, rfl⟩)⟩
  · rw [PMF.support_pure, Set.mem_singleton_iff] at h; subst h
    exact ⟨rfl, Or.inr (Or.inr ⟨h1, h2, rfl⟩)⟩

theorem aux_pec_step_inv {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (s s' : State M)
    (r : M) (hs : s.marked ⊆ s.covered ∧ s.covered.card = k) (h : s' ∈ (step k s r).support) :
    s'.marked = marksAfter k s.marked r ∧ s'.marked ⊆ s'.covered ∧ s'.covered.card = k ∧
      s'.covered ⊆ insert r s.covered := by
  obtain ⟨hm, hc⟩ := aux_pec_step_support k s s' r h
  obtain ⟨hs1, hs2⟩ := hs
  refine ⟨hm, ?_⟩
  rcases hc with ⟨hr, hc⟩ | ⟨hr, v, hv, hc⟩ | ⟨hr, hne, hc⟩
  · refine ⟨?_, by rw [hc]; exact hs2, by rw [hc]; exact Finset.subset_insert _ _⟩
    rw [hm, hc]
    intro x hx
    have := aux_pec_marksAfter_subset k s.marked r hx
    rw [Finset.mem_insert] at this
    rcases this with rfl | hx'
    · exact hr
    · exact hs1 hx'
  · rw [Finset.mem_sdiff] at hv
    refine ⟨?_, ?_, ?_⟩
    · rw [hm, hc]
      intro x hx
      have := aux_pec_marksAfter_subset k s.marked r hx
      rw [Finset.mem_insert] at this
      rcases this with rfl | hx'
      · exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        rw [Finset.mem_erase]
        exact ⟨fun hxv => hv.2 (hxv ▸ hx), hs1 hx'⟩
    · rw [hc, Finset.card_insert_of_notMem (fun h => hr (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hv.1]
      have : 0 < s.covered.card := Finset.card_pos.2 ⟨v, hv.1⟩
      omega
    · rw [hc]; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _)
  · exfalso
    apply hne
    by_cases h1 : (insert r s.marked).card = k + 1
    · have : marksAfter k s.marked r = {r} := by unfold marksAfter; rw [if_pos h1]
      rw [this]
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < s.covered.card)
      refine ⟨x, Finset.mem_sdiff.2 ⟨hx, ?_⟩⟩
      rw [Finset.mem_singleton]
      rintro rfl
      exact hr hx
    · have : marksAfter k s.marked r = insert r s.marked := by
        unfold marksAfter; rw [if_neg h1]
      rw [this]
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hcon
      have hsub : s.covered ⊆ s.marked := by
        intro x hx
        have := hcon hx
        rw [Finset.mem_insert] at this
        rcases this with rfl | h
        · exact absurd hx hr
        · exact h
      have heq : s.marked = s.covered := Finset.Subset.antisymm hs1 hsub
      apply h1
      rw [Finset.card_insert_of_notMem (by rw [heq]; exact hr), heq, hs2]

theorem aux_pec_take_succ {M : Type*} (σ : List M) (t : ℕ) (ht : t < σ.length) :
    σ.take (t + 1) = σ.take t ++ [σ.get ⟨t, ht⟩] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht]; rfl

theorem aux_pec_lawAfter_succ {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (σ : List M)
    (t : ℕ) (ht : t < σ.length) :
    lawAfter k V (σ.take (t + 1)) =
      (lawAfter k V (σ.take t)).bind (fun s => step k s (σ.get ⟨t, ht⟩)) := by
  unfold lawAfter; rw [aux_pec_take_succ σ t ht, List.foldl_append]; rfl

theorem aux_pec_marksAt_succ {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (σ : List M)
    (t : ℕ) (ht : t < σ.length) :
    marksAt k V σ (t + 1) = marksAfter k (marksAt k V σ t) (σ.get ⟨t, ht⟩) := by
  unfold marksAt; rw [aux_pec_take_succ σ t ht, List.foldl_append]; rfl

theorem aux_pec_foldl_inv {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (l : List M) :
    ∀ (p : PMF (State M)) (mk : Finset M),
    (∀ s ∈ p.support, s.marked = mk ∧ s.marked ⊆ s.covered ∧ s.covered.card = k) →
    ∀ s ∈ (l.foldl (fun p r => p.bind (fun s => step k s r)) p).support,
      s.marked = l.foldl (marksAfter k) mk ∧ s.marked ⊆ s.covered ∧ s.covered.card = k := by
  induction l with
  | nil => intro p mk h; simpa using h
  | cons r l ih =>
    intro p mk h
    simp only [List.foldl_cons]
    apply ih
    intro s hs
    rw [PMF.mem_support_bind_iff] at hs
    obtain ⟨s0, hs0, hs⟩ := hs
    obtain ⟨h1, h2, h3⟩ := h s0 hs0
    obtain ⟨g1, g2, g3, -⟩ := aux_pec_step_inv k hk s0 s r ⟨h2, h3⟩ hs
    exact ⟨by rw [g1, h1], g2, g3⟩

theorem aux_pec_card_initVertices {M : Type*} [DecidableEq M] {n k : ℕ} (e : Fin n ≃ M)
    (hkn : k ≤ n) : (initVertices e hkn).card = k := by
  unfold initVertices
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    unfold initConfig at h
    exact Fin.castLE_injective hkn (e.injective h)

theorem aux_pec_law_inv {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (V : Finset M)
    (hV : V.card = k) (σ : List M) (t : ℕ) :
    ∀ s ∈ (lawAfter k V (σ.take t)).support,
      s.marked = marksAt k V σ t ∧ s.marked ⊆ s.covered ∧ s.covered.card = k := by
  apply aux_pec_foldl_inv k hk
  intro s hs
  rw [PMF.support_pure, Set.mem_singleton_iff] at hs
  subst hs
  exact ⟨rfl, le_rfl, hV⟩

theorem aux_pec_card_marksAt {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (V : Finset M)
    (hV : V.card = k) (σ : List M) (t : ℕ) : (marksAt k V σ t).card ≤ k := by
  obtain ⟨s, hs⟩ := (lawAfter k V (σ.take t)).support_nonempty
  obtain ⟨h1, h2, h3⟩ := aux_pec_law_inv k hk V hV σ t s hs
  rw [← h1, ← h3]; exact Finset.card_le_card h2

theorem aux_pec_pR_self {M : Type*} [DecidableEq M] (σ : List M) (i : ℕ) :
    phaseRequested σ i i = ∅ := by
  simp [phaseRequested]

theorem aux_pec_pR_succ {M : Type*} [DecidableEq M] (σ : List M) (i t : ℕ) (hit : i ≤ t)
    (ht : t < σ.length) :
    phaseRequested σ i (t + 1) = insert (σ.get ⟨t, ht⟩) (phaseRequested σ i t) := by
  unfold phaseRequested
  rw [show t + 1 - i = (t - i) + 1 by omega, List.take_add_one, List.toFinset_append]
  rw [List.getElem?_drop, show i + (t - i) = t by omega, List.getElem?_eq_getElem ht]
  ext x
  simp [or_comm]

theorem aux_pec_pR_mono {M : Type*} [DecidableEq M] (σ : List M) (i t t' : ℕ) (h : t ≤ t') :
    phaseRequested σ i t ⊆ phaseRequested σ i t' := by
  unfold phaseRequested
  intro x hx
  rw [List.mem_toFinset] at hx ⊢
  exact (List.take_subset_take_left _ (by omega)) hx

def aux_pec_perm {M : Type*} (π : Equiv.Perm M) (s : State M) : State M :=
  ⟨s.covered.map π.toEmbedding, s.marked.map π.toEmbedding⟩

theorem aux_pec_marksAfter_map {M : Type*} [DecidableEq M] (k : ℕ) (π : Equiv.Perm M)
    (mk : Finset M) (r : M) :
    marksAfter k (mk.map π.toEmbedding) (π r) = (marksAfter k mk r).map π.toEmbedding := by
  unfold marksAfter
  have h : insert (π r) (mk.map π.toEmbedding) = (insert r mk).map π.toEmbedding := by
    rw [Finset.map_insert]; rfl
  rw [h, Finset.card_map]
  split_ifs
  · simp
  · rfl

theorem aux_pec_uniform_map {α β : Type*} (f : α ↪ β) (S : Finset α) (h : S.Nonempty)
    (h' : (S.map f).Nonempty) :
    PMF.uniformOfFinset (S.map f) h' = (PMF.uniformOfFinset S h).map f := by
  ext b
  rw [PMF.map_apply, PMF.uniformOfFinset_apply, Finset.card_map]
  by_cases hb : b ∈ S.map f
  · rw [if_pos hb]
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hb
    rw [tsum_eq_single a]
    · rw [if_pos rfl, PMF.uniformOfFinset_apply, if_pos ha]
    · intro a' ha'
      rw [if_neg]
      intro h; exact ha' (f.injective h).symm
  · rw [if_neg hb]
    symm
    apply ENNReal.tsum_eq_zero.2
    intro a
    split_ifs with h1
    · rw [PMF.uniformOfFinset_apply, if_neg]
      intro ha; exact hb (h1 ▸ Finset.mem_map_of_mem f ha)
    · rfl

theorem aux_pec_uniform_congr {α : Type*} (A B : Finset α) (hA : A.Nonempty) (hB : B.Nonempty)
    (h : A = B) : PMF.uniformOfFinset A hA = PMF.uniformOfFinset B hB := by
  subst h; rfl

theorem aux_pec_step_perm {M : Type*} [DecidableEq M] (k : ℕ) (π : Equiv.Perm M) (s : State M)
    (r : M) : step k (aux_pec_perm π s) (π r) = (step k s r).map (aux_pec_perm π) := by
  have hmk := aux_pec_marksAfter_map k π s.marked r
  have hmem : (π r ∈ s.covered.map π.toEmbedding) ↔ r ∈ s.covered := by simp
  have hsd : s.covered.map π.toEmbedding \ marksAfter k (s.marked.map π.toEmbedding) (π r) =
      (s.covered \ marksAfter k s.marked r).map π.toEmbedding := by
    rw [hmk, Finset.map_sdiff]
  by_cases h1 : r ∈ s.covered
  · have e1 : step k (aux_pec_perm π s) (π r) = PMF.pure
        ⟨s.covered.map π.toEmbedding, marksAfter k (s.marked.map π.toEmbedding) (π r)⟩ := by
      unfold step aux_pec_perm; simp only; rw [if_pos (hmem.2 h1)]
    have e2 : step k s r = PMF.pure ⟨s.covered, marksAfter k s.marked r⟩ := by
      unfold step; simp only; rw [if_pos h1]
    rw [e1, e2, PMF.pure_map, hmk]; rfl
  · by_cases h2 : (s.covered \ marksAfter k s.marked r).Nonempty
    · have h2m : ((s.covered \ marksAfter k s.marked r).map π.toEmbedding).Nonempty := h2.map
      have h2' : (s.covered.map π.toEmbedding \
          marksAfter k (s.marked.map π.toEmbedding) (π r)).Nonempty := by
        rw [hsd]; exact h2m
      have e1 : step k (aux_pec_perm π s) (π r) = (PMF.uniformOfFinset _ h2').map
          (fun v => (⟨insert (π r) ((s.covered.map π.toEmbedding).erase v),
            marksAfter k (s.marked.map π.toEmbedding) (π r)⟩ : State M)) := by
        unfold step aux_pec_perm; simp only; rw [if_neg (mt hmem.1 h1), dif_pos h2']
      have e2 : step k s r = (PMF.uniformOfFinset _ h2).map
          (fun v => (⟨insert r (s.covered.erase v), marksAfter k s.marked r⟩ : State M)) := by
        unfold step; simp only; rw [if_neg h1, dif_pos h2]
      rw [e1, e2, aux_pec_uniform_congr _ _ h2' h2m hsd, aux_pec_uniform_map _ _ h2 h2m,
        PMF.map_comp, PMF.map_comp]
      congr 1
      funext v
      simp [aux_pec_perm, Function.comp, Finset.map_insert, Finset.map_erase, hmk]
    · have h2' : ¬ (s.covered.map π.toEmbedding \
          marksAfter k (s.marked.map π.toEmbedding) (π r)).Nonempty := by
        rw [hsd, Finset.map_nonempty]; exact h2
      have e1 : step k (aux_pec_perm π s) (π r) = PMF.pure
          ⟨s.covered.map π.toEmbedding, marksAfter k (s.marked.map π.toEmbedding) (π r)⟩ := by
        unfold step aux_pec_perm; simp only; rw [if_neg (mt hmem.1 h1), dif_neg h2']
      have e2 : step k s r = PMF.pure ⟨s.covered, marksAfter k s.marked r⟩ := by
        unfold step; simp only; rw [if_neg h1, dif_neg h2]
      rw [e1, e2, PMF.pure_map, hmk]; rfl

theorem aux_pec_map_perm_step {M : Type*} [DecidableEq M] (k : ℕ) (π : Equiv.Perm M)
    (p : PMF (State M)) (r : M) (hr : π r = r) (hp : p.map (aux_pec_perm π) = p) :
    (p.bind (fun s => step k s r)).map (aux_pec_perm π) = p.bind (fun s => step k s r) := by
  rw [PMF.map_bind]
  have : ∀ s, (step k s r).map (aux_pec_perm π) = step k (aux_pec_perm π s) r := by
    intro s; rw [← aux_pec_step_perm, hr]
  simp_rw [this]
  conv_rhs => rw [← hp]
  rw [PMF.bind_map]; rfl

theorem aux_pec_map_swap_of_mem {M : Type*} [DecidableEq M] (S : Finset M) (v w : M)
    (hv : v ∈ S) (hw : w ∈ S) : S.map (Equiv.swap v w).toEmbedding = S := by
  ext x
  rw [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; simp [hv, hw]
  · subst h2; simp [hv, hw]
  · rfl

theorem aux_pec_map_eq_self {α : Type*} (p : PMF α) (f : α → α) (h : ∀ a ∈ p.support, f a = a) :
    p.map f = p := by
  ext b
  rw [PMF.map_apply]
  rw [tsum_eq_single b]
  · by_cases hb : b ∈ p.support
    · rw [if_pos (h b hb).symm]
    · rw [(PMF.apply_eq_zero_iff p b).2 hb]; simp
  · intro a hab
    by_cases ha : a ∈ p.support
    · rw [h a ha, if_neg (Ne.symm hab)]
    · rw [(PMF.apply_eq_zero_iff p a).2 ha]; simp

theorem aux_pec_prob_swap {M : Type*} [DecidableEq M] (p : PMF (State M)) (v w : M)
    (hp : p.map (aux_pec_perm (Equiv.swap v w)) = p) :
    p.toOuterMeasure {s | w ∉ s.covered} = p.toOuterMeasure {s | v ∉ s.covered} := by
  conv_lhs => rw [← hp]
  rw [PMF.toOuterMeasure_map_apply]
  congr 1
  ext s
  simp [aux_pec_perm, Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_right]

theorem aux_pec_sum_prob {M : Type*} [DecidableEq M] (p : PMF (State M)) (Q : Finset M) (c : ℕ)
    (h : ∀ s ∈ p.support, (Q \ s.covered).card = c) :
    ∑ v ∈ Q, p.toOuterMeasure {s | v ∉ s.covered} = c := by
  simp_rw [PMF.toOuterMeasure_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have : ∀ x, ∑ v ∈ Q, Set.indicator {s : State M | v ∉ s.covered} p x = p x * c := by
    intro x
    by_cases hx : x ∈ p.support
    · rw [← h x hx]
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        mul_comm, Finset.sdiff_eq_filter]
    · have hpx := (PMF.apply_eq_zero_iff p x).2 hx
      rw [hpx, zero_mul]
      simp [Set.indicator_apply, hpx]
  simp_rw [this]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem aux_pec_phase_basic {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (V : Finset M)
    (hV : V.card = k) (σ : List M) (t : ℕ) (ht : t < σ.length)
    (hc : (insert (σ.get ⟨t, ht⟩) (marksAt k V σ t)).card = k + 1) :
    (marksAt k V σ t).card = k ∧ σ.get ⟨t, ht⟩ ∉ marksAt k V σ t := by
  have h1 := aux_pec_card_marksAt k hk V hV σ t
  by_cases hm : σ.get ⟨t, ht⟩ ∈ marksAt k V σ t
  · rw [Finset.insert_eq_of_mem hm] at hc; omega
  · rw [Finset.card_insert_of_notMem hm] at hc; exact ⟨by omega, hm⟩

theorem aux_pec_marks_phase {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (V : Finset M)
    (hV : V.card = k) (σ : List M) (i i' : ℕ) (hphase : IsCompletePhase k V σ i i') :
    ∀ d, i + 1 + d ≤ i' → marksAt k V σ (i + 1 + d) = phaseRequested σ i (i + 1 + d) := by
  obtain ⟨⟨hil, hic⟩, ⟨hi'l, hi'c⟩, hii', hno⟩ := hphase
  intro d
  induction d with
  | zero =>
    intro _
    rw [add_zero, aux_pec_marksAt_succ k V σ i hil, aux_pec_pR_succ σ i i le_rfl hil,
      aux_pec_pR_self]
    unfold marksAfter
    rw [if_pos hic]
    rfl
  | succ d ih =>
    intro hd
    have ht : i + 1 + d < σ.length := by omega
    rw [show i + 1 + (d + 1) = (i + 1 + d) + 1 by omega, aux_pec_marksAt_succ k V σ _ ht,
      aux_pec_pR_succ σ i _ (by omega) ht, ← ih (by omega)]
    unfold marksAfter
    rw [if_neg]
    intro hc
    exact hno (i + 1 + d) (by omega) (by omega) ⟨ht, hc⟩

theorem aux_pec_cov_phase {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (V : Finset M)
    (hV : V.card = k) (σ : List M) (i i' : ℕ) (hphase : IsCompletePhase k V σ i i') :
    ∀ d, i + d ≤ i' → ∀ s ∈ (lawAfter k V (σ.take (i + d))).support,
      s.covered ⊆ marksAt k V σ i ∪ phaseRequested σ i (i + d) := by
  obtain ⟨⟨hil, hic⟩, ⟨hi'l, hi'c⟩, hii', hno⟩ := hphase
  obtain ⟨hPk, hσi⟩ := aux_pec_phase_basic k hk V hV σ i hil hic
  intro d
  induction d with
  | zero =>
    intro _ s hs
    rw [add_zero] at hs ⊢
    obtain ⟨h1, h2, h3⟩ := aux_pec_law_inv k hk V hV σ i s hs
    have : marksAt k V σ i = s.covered :=
      Finset.eq_of_subset_of_card_le (h1 ▸ h2) (by rw [h3, hPk])
    rw [aux_pec_pR_self, Finset.union_empty, this]
  | succ d ih =>
    intro hd s hs
    have ht : i + d < σ.length := by omega
    rw [← add_assoc, aux_pec_lawAfter_succ k V σ _ ht, PMF.mem_support_bind_iff] at hs
    obtain ⟨s0, hs0, hs⟩ := hs
    obtain ⟨a1, a2, a3⟩ := aux_pec_law_inv k hk V hV σ _ s0 hs0
    obtain ⟨-, -, -, g4⟩ := aux_pec_step_inv k hk s0 s _ ⟨a2, a3⟩ hs
    have := ih (by omega) s0 hs0
    rw [← add_assoc, aux_pec_pR_succ σ i _ (by omega) ht]
    intro x hx
    have hx' := g4 hx
    rw [Finset.mem_insert] at hx'
    rcases hx' with rfl | hx'
    · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    · rcases Finset.mem_union.1 (this hx') with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem h)

theorem aux_pec_swap_phase {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (V : Finset M)
    (hV : V.card = k) (σ : List M) (i i' : ℕ) (hphase : IsCompletePhase k V σ i i') :
    ∀ d, i + d ≤ i' → ∀ v w, v ∈ marksAt k V σ i \ phaseRequested σ i (i + d) →
      w ∈ marksAt k V σ i \ phaseRequested σ i (i + d) →
      (lawAfter k V (σ.take (i + d))).map (aux_pec_perm (Equiv.swap v w)) =
        lawAfter k V (σ.take (i + d)) := by
  obtain ⟨⟨hil, hic⟩, ⟨hi'l, hi'c⟩, hii', hno⟩ := hphase
  obtain ⟨hPk, hσi⟩ := aux_pec_phase_basic k hk V hV σ i hil hic
  intro d
  induction d with
  | zero =>
    intro _ v w hv hw
    rw [add_zero] at hv hw ⊢
    rw [aux_pec_pR_self, Finset.sdiff_empty] at hv hw
    apply aux_pec_map_eq_self
    intro s hs
    obtain ⟨h1, h2, h3⟩ := aux_pec_law_inv k hk V hV σ i s hs
    have e1 : s.covered = marksAt k V σ i :=
      (Finset.eq_of_subset_of_card_le (h1 ▸ h2) (by rw [h3, hPk])).symm
    cases s with
    | mk C Mk =>
      simp only at e1 h1
      subst e1 h1
      simp only [aux_pec_perm, aux_pec_map_swap_of_mem _ v w hv hw]
  | succ d ih =>
    intro hd v w hv hw
    have ht : i + d < σ.length := by omega
    rw [← add_assoc] at hv hw ⊢
    rw [aux_pec_lawAfter_succ k V σ _ ht]
    rw [aux_pec_pR_succ σ i _ (by omega) ht] at hv hw
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hv hw
    apply aux_pec_map_perm_step
    · exact Equiv.swap_apply_of_ne_of_ne (fun h => hv.2.1 h.symm) (fun h => hw.2.1 h.symm)
    · exact ih (by omega) v w (Finset.mem_sdiff.2 ⟨hv.1, hv.2.2⟩)
        (Finset.mem_sdiff.2 ⟨hw.1, hw.2.2⟩)

theorem aux_pec_le_one {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (l : List M) (r : M) :
    (faultProb k V l r).toReal ≤ 1 := by
  unfold faultProb
  have h : (lawAfter k V l).toOuterMeasure {s | r ∉ s.covered} ≤ 1 := by
    rw [← (PMF.toOuterMeasure_apply_eq_one_iff _ Set.univ).2 (Set.subset_univ _)]
    exact (lawAfter k V l).toOuterMeasure.mono (Set.subset_univ _)
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)

theorem aux_pec_repeat {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (V : Finset M)
    (hV : V.card = k) (σ : List M) (i i' : ℕ) (hphase : IsCompletePhase k V σ i i') (t : ℕ)
    (hit : i < t) (hti' : t ≤ i') (r : M) (hr : r ∈ phaseRequested σ i t) :
    (faultProb k V (σ.take t) r).toReal = 0 := by
  have hM1 := aux_pec_marks_phase k hk V hV σ i i' hphase (t - (i + 1)) (by omega)
  rw [show i + 1 + (t - (i + 1)) = t by omega] at hM1
  unfold faultProb
  rw [(PMF.toOuterMeasure_apply_eq_zero_iff _ _).2]
  · rfl
  · rw [Set.disjoint_left]
    intro s hs hns
    obtain ⟨h1, h2, -⟩ := aux_pec_law_inv k hk V hV σ t s hs
    have : r ∈ s.marked := by rw [h1, hM1]; exact hr
    exact hns (h2 this)

theorem aux_pec_stale {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (V : Finset M)
    (hV : V.card = k) (σ : List M) (i i' : ℕ) (hphase : IsCompletePhase k V σ i i') (t : ℕ)
    (hit : i < t) (hti' : t ≤ i') (r : M)
    (hr : r ∈ marksAt k V σ i \ phaseRequested σ i t) :
    (faultProb k V (σ.take t) r).toReal * ((marksAt k V σ i \ phaseRequested σ i t).card : ℝ) =
      ((phaseRequested σ i t \ marksAt k V σ i).card : ℝ) := by
  have hM1 := aux_pec_marks_phase k hk V hV σ i i' hphase (t - (i + 1)) (by omega)
  rw [show i + 1 + (t - (i + 1)) = t by omega] at hM1
  have hB := aux_pec_cov_phase k hk V hV σ i i' hphase (t - i) (by omega)
  rw [show i + (t - i) = t by omega] at hB
  have hC := aux_pec_swap_phase k hk V hV σ i i' hphase (t - i) (by omega)
  rw [show i + (t - i) = t by omega] at hC
  have hPk : (marksAt k V σ i).card = k :=
    (aux_pec_phase_basic k hk V hV σ i hphase.1.1 hphase.1.2).1
  have hcount : ∀ s ∈ (lawAfter k V (σ.take t)).support,
      ((marksAt k V σ i \ phaseRequested σ i t) \ s.covered).card =
        (phaseRequested σ i t \ marksAt k V σ i).card := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := aux_pec_law_inv k hk V hV σ t s hs
    have hcov := hB s hs
    rw [h1, hM1] at h2
    have e1 : (marksAt k V σ i \ phaseRequested σ i t) ∩ s.covered =
        s.covered \ phaseRequested σ i t := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨_, hx⟩, hc⟩; exact ⟨hc, hx⟩
      · rintro ⟨hc, hx⟩
        refine ⟨⟨?_, hx⟩, hc⟩
        rcases Finset.mem_union.1 (hcov hc) with h | h
        · exact h
        · exact absurd h hx
    have c1 := Finset.card_sdiff_add_card_inter
      (marksAt k V σ i \ phaseRequested σ i t) s.covered
    have c2 := Finset.card_sdiff_add_card_inter (marksAt k V σ i) (phaseRequested σ i t)
    have c3 := Finset.card_sdiff_add_card_inter (phaseRequested σ i t) (marksAt k V σ i)
    have c4 := Finset.card_sdiff_add_card_inter s.covered (phaseRequested σ i t)
    rw [Finset.inter_eq_right.2 h2] at c4
    rw [e1] at c1
    rw [Finset.inter_comm] at c3
    omega
  have hsum := aux_pec_sum_prob _ _ _ hcount
  have heq : ∀ v ∈ marksAt k V σ i \ phaseRequested σ i t,
      (lawAfter k V (σ.take t)).toOuterMeasure {s | v ∉ s.covered} =
        (lawAfter k V (σ.take t)).toOuterMeasure {s | r ∉ s.covered} := by
    intro v hv
    exact aux_pec_prob_swap _ r v (hC r v hr hv)
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul] at hsum
  unfold faultProb
  have := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this
  rw [mul_comm]; exact this

noncomputable def aux_pec_G {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (σ : List M)
    (i t : ℕ) : ℝ :=
  ∑ u : Fin σ.length,
    if i ≤ u.val ∧ u.val < t then (faultProb k V (σ.take u) (σ.get u)).toReal else 0

theorem aux_pec_G_succ {M : Type*} [DecidableEq M] (k : ℕ) (V : Finset M) (σ : List M)
    (i t : ℕ) (ht : t < σ.length) (hit : i ≤ t) :
    aux_pec_G k V σ i (t + 1) =
      aux_pec_G k V σ i t + (faultProb k V (σ.take t) (σ.get ⟨t, ht⟩)).toReal := by
  unfold aux_pec_G
  have : ∀ u : Fin σ.length,
      (if i ≤ u.val ∧ u.val < t + 1 then (faultProb k V (σ.take u) (σ.get u)).toReal else 0) =
      (if i ≤ u.val ∧ u.val < t then (faultProb k V (σ.take u) (σ.get u)).toReal else 0) +
      (if u = ⟨t, ht⟩ then (faultProb k V (σ.take u) (σ.get u)).toReal else 0) := by
    intro u
    by_cases h1 : u = ⟨t, ht⟩
    · subst h1; simp [hit]
    · have : u.val ≠ t := fun h => h1 (Fin.ext h)
      by_cases h2 : i ≤ u.val ∧ u.val < t
      · rw [if_pos ⟨h2.1, by omega⟩, if_pos h2, if_neg h1, add_zero]
      · rw [if_neg (by omega), if_neg h2, if_neg h1, add_zero]
  rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem aux_pec_main {M : Type*} [DecidableEq M] (k : ℕ) (hk : 1 ≤ k) (V : Finset M)
    (hV : V.card = k) (σ : List M) (i i' : ℕ) (hphase : IsCompletePhase k V σ i i') :
    markingPhaseCost k V σ i i' ≤
      ((phaseRequested σ i i' \ marksAt k V σ i).card : ℝ) *
        ((harmonic k : ℝ) - (harmonic (phaseRequested σ i i' \ marksAt k V σ i).card : ℝ)
          + 1) := by
  have hphase' := hphase
  obtain ⟨⟨hil, hic⟩, ⟨hi'l, hi'c⟩, hii', hno⟩ := hphase'
  obtain ⟨hPk, hσi⟩ := aux_pec_phase_basic k hk V hV σ i hil hic
  obtain ⟨hRk', -⟩ := aux_pec_phase_basic k hk V hV σ i' hi'l hi'c
  have key : ∀ d, i + d ≤ i' →
      aux_pec_G k V σ i (i + d) ≤
        ((phaseRequested σ i (i + d) \ marksAt k V σ i).card : ℝ) +
          ((phaseRequested σ i i' \ marksAt k V σ i).card : ℝ) *
            ((harmonic k : ℝ) -
              (harmonic (k - (phaseRequested σ i (i + d) ∩ marksAt k V σ i).card) : ℝ)) := by
    intro d
    induction d with
    | zero =>
      intro _
      have : aux_pec_G k V σ i i = 0 := by
        unfold aux_pec_G
        exact Finset.sum_eq_zero (fun u _ => if_neg (by omega))
      simp [this, aux_pec_pR_self]
    | succ d ih =>
      intro hd
      have ih' := ih (by omega)
      have ht : i + d < σ.length := by omega
      rw [← add_assoc, aux_pec_G_succ k V σ i _ ht (by omega),
        aux_pec_pR_succ σ i _ (by omega) ht]
      have hl_nonneg : (0 : ℝ) ≤ ((phaseRequested σ i i' \ marksAt k V σ i).card : ℝ) :=
        Nat.cast_nonneg _
      by_cases hrR : σ.get ⟨i + d, ht⟩ ∈ phaseRequested σ i (i + d)
      · have hit : i < i + d := by
          rcases Nat.eq_zero_or_pos d with h | h
          · subst h; simp [aux_pec_pR_self] at hrR
          · omega
        rw [aux_pec_repeat k hk V hV σ i i' hphase (i + d) hit (by omega) _ hrR,
          Finset.insert_eq_of_mem hrR]
        linarith
      · by_cases hrP : σ.get ⟨i + d, ht⟩ ∈ marksAt k V σ i
        · have hit : i < i + d := by
            rcases Nat.eq_zero_or_pos d with h | h
            · subst h; exact absurd hrP hσi
            · omega
          have hst := aux_pec_stale k hk V hV σ i i' hphase (i + d) hit (by omega) _
            (Finset.mem_sdiff.2 ⟨hrP, hrR⟩)
          rw [Finset.insert_sdiff_of_mem _ hrP, Finset.insert_inter_of_mem hrP,
            Finset.card_insert_of_notMem (fun h => hrR (Finset.mem_inter.1 h).1)]
          set c := (phaseRequested σ i (i + d) \ marksAt k V σ i).card with hc
          set sI := (phaseRequested σ i (i + d) ∩ marksAt k V σ i).card with hsI
          set l := (phaseRequested σ i i' \ marksAt k V σ i).card with hl
          set m := (marksAt k V σ i \ phaseRequested σ i (i + d)).card with hm
          have c2 := Finset.card_sdiff_add_card_inter (marksAt k V σ i)
            (phaseRequested σ i (i + d))
          rw [Finset.inter_comm] at c2
          have hmpos : 0 < m := Finset.card_pos.2 ⟨_, Finset.mem_sdiff.2 ⟨hrP, hrR⟩⟩
          have hm2 : k - sI = (k - (sI + 1)) + 1 := by omega
          have hm3 : m = (k - (sI + 1)) + 1 := by omega
          have hcl : c ≤ l := Finset.card_le_card
            (Finset.sdiff_subset_sdiff (aux_pec_pR_mono σ i _ _ (by omega)) le_rfl)
          have hH : (harmonic (k - sI) : ℝ) =
              (harmonic (k - (sI + 1)) : ℝ) + 1 / (m : ℝ) := by
            rw [hm2, harmonic_succ, hm3]
            push_cast
            ring
          rw [hH] at ih'
          have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
          have hpf : (faultProb k V (σ.take (i + d)) (σ.get ⟨i + d, ht⟩)).toReal = c / m := by
            rw [eq_div_iff hmR.ne']; exact hst
          rw [hpf]
          have hcl' : (c : ℝ) / m ≤ l / m :=
            div_le_div_of_nonneg_right (by exact_mod_cast hcl) hmR.le
          have : (l : ℝ) * (1 / m) = l / m := by ring
          nlinarith
        · have h1 := aux_pec_le_one k V (σ.take (i + d)) (σ.get ⟨i + d, ht⟩)
          rw [Finset.insert_sdiff_of_notMem _ hrP, Finset.insert_inter_of_notMem hrP,
            Finset.card_insert_of_notMem (fun h => hrR (Finset.mem_sdiff.1 h).1)]
          push_cast
          linarith
  have hfin := key (i' - i) (by omega)
  rw [show i + (i' - i) = i' by omega] at hfin
  have hM1 := aux_pec_marks_phase k hk V hV σ i i' hphase (i' - (i + 1)) (by omega)
  rw [show i + 1 + (i' - (i + 1)) = i' by omega] at hM1
  rw [hM1] at hRk'
  have c3 := Finset.card_sdiff_add_card_inter (phaseRequested σ i i') (marksAt k V σ i)
  have hkl : k - (phaseRequested σ i i' ∩ marksAt k V σ i).card =
      (phaseRequested σ i i' \ marksAt k V σ i).card := by omega
  rw [hkl] at hfin
  show aux_pec_G k V σ i i' ≤ _
  linarith

end CompetitivePaging.Marking

open CompetitivePaging.Marking

theorem solution {n k : ℕ} {M : Type*} [DecidableEq M]
    (e : Fin n ≃ M) (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    markingPhaseCost k (initVertices e hkn) σ i i'
        ≤ ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          * ((harmonic k : ℝ)
            - (harmonic (phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
            + 1) ∧
      ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          * ((harmonic k : ℝ)
            - (harmonic (phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
            + 1)
        ≤ ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          * (harmonic k : ℝ) := by
  refine ⟨aux_pec_main k hk _ (aux_pec_card_initVertices e hkn) σ i i' hphase, ?_⟩
  set l := (phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card
  rcases Nat.eq_zero_or_pos l with h | h
  · rw [h]; simp
  · have hHq : (1 : ℚ) ≤ harmonic l := by
      unfold harmonic
      have := Finset.single_le_sum (s := Finset.range l) (f := fun i : ℕ => ((↑(i + 1) : ℚ))⁻¹)
        (fun _ _ => by positivity) (Finset.mem_range.2 h)
      simpa using this
    have hH : (1 : ℝ) ≤ (harmonic l : ℝ) := by exact_mod_cast hHq
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg _
    nlinarith
