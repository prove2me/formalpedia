-- Prove2me | solution 1 for CompetitivePaging.Marking.stale_fault_prob
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:58:37.05499+00:00
-- url     : https://prove2.me/submissions/6dea86ac-d9f9-49c9-8698-e0a0b5a65369

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

open scoped ENNReal

namespace CompetitivePaging.Marking

section aux_sfp_section

variable {M : Type*} [DecidableEq M]

lemma aux_sfp_marksAfter_subset (k : ℕ) (mk : Finset M) (r : M) :
    marksAfter k mk r ⊆ insert r mk := by
  unfold marksAfter
  split_ifs
  · simp
  · exact Finset.Subset.refl _

lemma aux_sfp_mem_marksAfter (k : ℕ) (mk : Finset M) (r : M) : r ∈ marksAfter k mk r := by
  unfold marksAfter
  split_ifs <;> simp

lemma aux_sfp_marksAfter_card (k : ℕ) (hk : 1 ≤ k) (mk : Finset M) (r : M) (h : mk.card ≤ k) :
    (marksAfter k mk r).card ≤ k := by
  unfold marksAfter
  split_ifs with h1
  · simpa using hk
  · have := Finset.card_insert_le r mk
    omega

lemma aux_sfp_step_cov (k : ℕ) (s s' : State M) (r : M) (h : s' ∈ (step k s r).support) :
    s'.covered ⊆ insert r s.covered := by
  unfold step at h
  simp only at h
  split_ifs at h with h1 h2
  · rw [PMF.mem_support_pure_iff] at h
    subst h
    exact Finset.subset_insert _ _
  · rw [PMF.mem_support_map_iff] at h
    obtain ⟨v, -, rfl⟩ := h
    exact Finset.insert_subset_insert _ (Finset.erase_subset _ _)
  · rw [PMF.mem_support_pure_iff] at h
    subst h
    exact Finset.subset_insert _ _

lemma aux_sfp_step_supp (k : ℕ) (hk : 1 ≤ k) (s s' : State M) (r : M)
    (hsub : s.marked ⊆ s.covered) (hcard : s.covered.card = k) (hmk : s.marked.card ≤ k)
    (h : s' ∈ (step k s r).support) :
    s'.marked = marksAfter k s.marked r ∧ s'.marked ⊆ s'.covered ∧ s'.covered.card = k ∧
      s'.marked.card ≤ k := by
  have hmc := aux_sfp_marksAfter_card k hk s.marked r hmk
  have hms := aux_sfp_marksAfter_subset k s.marked r
  have hrm := aux_sfp_mem_marksAfter k s.marked r
  unfold step at h
  simp only at h
  split_ifs at h with h1 h2
  · rw [PMF.mem_support_pure_iff] at h
    subst h
    exact ⟨rfl, hms.trans (Finset.insert_subset h1 hsub), hcard, hmc⟩
  · rw [PMF.mem_support_map_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    rw [PMF.mem_support_uniformOfFinset_iff, Finset.mem_sdiff] at hv
    refine ⟨rfl, ?_, ?_, hmc⟩
    · intro x hx
      have hx' := hms hx
      rw [Finset.mem_insert] at hx' ⊢
      rcases hx' with hx' | hx'
      · exact Or.inl hx'
      · right
        rw [Finset.mem_erase]
        exact ⟨fun hxv => hv.2 (hxv ▸ hx), hsub hx'⟩
    · rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem hv.1, hcard]
      · omega
      · intro hr
        exact h1 (Finset.mem_of_mem_erase hr)
  · exfalso
    have hsub2 : s.covered ⊆ marksAfter k s.marked r := by
      intro x hx
      by_contra hx'
      exact h2 ⟨x, Finset.mem_sdiff.2 ⟨hx, hx'⟩⟩
    have := Finset.card_le_card (Finset.insert_subset hrm hsub2)
    rw [Finset.card_insert_of_notMem h1] at this
    omega

lemma aux_sfp_law_append (k : ℕ) (V : Finset M) (l1 l2 : List M) :
    lawAfter k V (l1 ++ l2) =
      l2.foldl (fun p r => p.bind (fun s => step k s r)) (lawAfter k V l1) := by
  simp only [lawAfter, List.foldl_append]

lemma aux_sfp_invA (k : ℕ) (hk : 1 ≤ k) (V : Finset M) (hV : V.card = k) (l : List M) :
    ∀ s ∈ (lawAfter k V l).support, s.marked = l.foldl (marksAfter k) V ∧
      s.marked ⊆ s.covered ∧ s.covered.card = k ∧ s.marked.card ≤ k := by
  induction l using List.reverseRecOn with
  | nil =>
    intro s hs
    simp only [lawAfter, List.foldl_nil, PMF.mem_support_pure_iff] at hs
    subst hs
    exact ⟨rfl, Finset.Subset.refl _, hV, hV.le⟩
  | append_singleton l r ih =>
    intro s hs
    rw [aux_sfp_law_append, List.foldl_cons, List.foldl_nil, PMF.mem_support_bind_iff] at hs
    obtain ⟨s0, hs0, hs⟩ := hs
    obtain ⟨h1, h2, h3, h4⟩ := ih s0 hs0
    obtain ⟨g1, g2, g3, g4⟩ := aux_sfp_step_supp k hk s0 s r h2 h3 h4 hs
    refine ⟨?_, g2, g3, g4⟩
    rw [g1, h1, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma aux_sfp_invB (k : ℕ) (L : List M) : ∀ (p : PMF (State M)) (X : Finset M),
    (∀ s ∈ p.support, s.covered ⊆ X) →
    ∀ s ∈ (L.foldl (fun p r => p.bind (fun s => step k s r)) p).support,
      s.covered ⊆ X ∪ L.toFinset := by
  induction L with
  | nil =>
    intro p X h s hs
    simpa using h s hs
  | cons r L ih =>
    intro p X h s hs
    rw [List.foldl_cons] at hs
    have := ih _ (insert r X) (by
      intro s' hs'
      rw [PMF.mem_support_bind_iff] at hs'
      obtain ⟨s0, hs0, hs'⟩ := hs'
      exact (aux_sfp_step_cov k s0 s' r hs').trans
        (Finset.insert_subset_insert _ (h s0 hs0))) s hs
    intro x hx
    have := this hx
    simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons, List.mem_toFinset]
      at this ⊢
    tauto

/-- Relabel the vertices of a state by a permutation. -/
def aux_sfp_act (π : Equiv.Perm M) (s : State M) : State M :=
  ⟨s.covered.map π.toEmbedding, s.marked.map π.toEmbedding⟩

lemma aux_sfp_marksAfter_map (k : ℕ) (π : Equiv.Perm M) (mk : Finset M) (r : M) :
    marksAfter k (mk.map π.toEmbedding) (π r) = (marksAfter k mk r).map π.toEmbedding := by
  unfold marksAfter
  have : insert (π r) (mk.map π.toEmbedding) = (insert r mk).map π.toEmbedding := by
    rw [Finset.map_insert]
    rfl
  rw [this, Finset.card_map]
  split_ifs
  · simp
  · rfl

lemma aux_sfp_unif_map (π : Equiv.Perm M) (A B : Finset M) (hA : A.Nonempty)
    (hB : B.Nonempty) (hAB : B = A.map π.toEmbedding) :
    PMF.uniformOfFinset B hB = (PMF.uniformOfFinset A hA).map π := by
  subst hAB
  ext b
  rw [PMF.map_apply, tsum_eq_single (π.symm b)]
  · simp [PMF.uniformOfFinset_apply, Finset.mem_map_equiv]
  · intro a ha
    rw [if_neg]
    intro hb
    apply ha
    rw [hb]
    simp

lemma aux_sfp_step_equiv (k : ℕ) (π : Equiv.Perm M) (s : State M) (r : M) :
    step k (aux_sfp_act π s) (π r) = (step k s r).map (aux_sfp_act π) := by
  unfold step aux_sfp_act
  simp only [aux_sfp_marksAfter_map]
  have hmem : (π r ∈ s.covered.map π.toEmbedding) ↔ r ∈ s.covered := by
    simpa using Finset.mem_map' π.toEmbedding (a := r) (s := s.covered)
  have hsd : s.covered.map π.toEmbedding \ (marksAfter k s.marked r).map π.toEmbedding
      = (s.covered \ marksAfter k s.marked r).map π.toEmbedding := (Finset.map_sdiff _ _).symm
  by_cases h1 : r ∈ s.covered
  · rw [if_pos (hmem.2 h1), if_pos h1, PMF.pure_map]
  · rw [if_neg (mt hmem.1 h1), if_neg h1]
    by_cases h2 : (s.covered \ marksAfter k s.marked r).Nonempty
    · have h2' : (s.covered.map π.toEmbedding \
          (marksAfter k s.marked r).map π.toEmbedding).Nonempty := by
        rw [hsd]
        exact h2.map
      rw [dif_pos h2, dif_pos h2', aux_sfp_unif_map π _ _ h2 h2' hsd, PMF.map_comp,
        PMF.map_comp]
      congr 1
      funext v
      simp [Finset.map_insert, Finset.map_erase]
    · have h2' : ¬ (s.covered.map π.toEmbedding \
          (marksAfter k s.marked r).map π.toEmbedding).Nonempty := by
        rw [hsd, Finset.map_nonempty]
        exact h2
      rw [dif_neg h2, dif_neg h2', PMF.pure_map]

lemma aux_sfp_fold_equiv (k : ℕ) (π : Equiv.Perm M) (L : List M) : ∀ p : PMF (State M),
    (L.map π).foldl (fun p r => p.bind (fun s => step k s r)) (p.map (aux_sfp_act π)) =
      (L.foldl (fun p r => p.bind (fun s => step k s r)) p).map (aux_sfp_act π) := by
  induction L with
  | nil => intro p; rfl
  | cons r L ih =>
    intro p
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    rw [PMF.bind_map, PMF.map_bind]
    congr 1
    funext s
    exact aux_sfp_step_equiv k π s r

lemma aux_sfp_map_fix {α : Type*} (p : PMF α) (f : α → α) (h : ∀ a ∈ p.support, f a = a) :
    p.map f = p := by
  ext b
  rw [PMF.map_apply, tsum_eq_single b]
  · by_cases hb : b ∈ p.support
    · rw [h b hb, if_pos rfl]
    · have : p b = 0 := (PMF.apply_eq_zero_iff p b).2 hb
      simp [this]
  · intro a ha
    by_cases hs : a ∈ p.support
    · rw [h a hs, if_neg (Ne.symm ha)]
    · rw [(PMF.apply_eq_zero_iff p a).2 hs]
      simp

lemma aux_sfp_map_swap (A : Finset M) (x y : M) (hx : x ∈ A) (hy : y ∈ A) :
    A.map (Equiv.swap x y).toEmbedding = A := by
  ext z
  rw [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1
    simp [hx, hy]
  · subst h2
    simp [hx, hy]
  · rfl

lemma aux_sfp_marksAt_succ (k : ℕ) (V : Finset M) (σ : List M) (u : ℕ) (hu : u < σ.length) :
    marksAt k V σ (u+1) = marksAfter k (marksAt k V σ u) (σ.get ⟨u, hu⟩) := by
  unfold marksAt
  rw [List.take_add_one, List.getElem?_eq_getElem hu, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  rfl

lemma aux_sfp_phaseReq_succ (σ : List M) (i u : ℕ) (hiu : i ≤ u) (hu : u < σ.length) :
    phaseRequested σ i (u+1) = insert (σ.get ⟨u, hu⟩) (phaseRequested σ i u) := by
  unfold phaseRequested
  rw [show u + 1 - i = (u - i) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show i + (u - i) = u by omega, List.getElem?_eq_getElem hu]
  ext x
  simp [List.toFinset_append]

lemma aux_sfp_phaseReq_self (σ : List M) (i : ℕ) : phaseRequested σ i i = ∅ := by
  simp [phaseRequested]

end aux_sfp_section

end CompetitivePaging.Marking

open CompetitivePaging.Marking
open scoped ENNReal

theorem solution {n k : ℕ} {M : Type*} [DecidableEq M]
    (e : Fin n ≃ M) (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (i t : ℕ) (ht : t < σ.length)
    (hi : IsPhaseStart k (initVertices e hkn) σ i) (hit : i ≤ t)
    (hno : ∀ u, i < u → u ≤ t → ¬ IsPhaseStart k (initVertices e hkn) σ u)
    (hstale : σ.get ⟨t, ht⟩ ∈ marksAt k (initVertices e hkn) σ i)
    (hnew : σ.get ⟨t, ht⟩ ∉ phaseRequested σ i t) :
    faultProb k (initVertices e hkn) (σ.take t) (σ.get ⟨t, ht⟩) =
      ((phaseRequested σ i t \ marksAt k (initVertices e hkn) σ i).card : ℝ≥0∞)
        / ((marksAt k (initVertices e hkn) σ i \ phaseRequested σ i t).card : ℝ≥0∞) := by
  have hV : (initVertices e hkn).card = k := by
    unfold initVertices
    rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
    intro a b hab
    exact Fin.castLE_injective hkn (e.injective hab)
  obtain ⟨hi_lt, hiph⟩ := hi
  set V := initVertices e hkn with hVdef
  set Mi := marksAt k V σ i with hMi
  set P := phaseRequested σ i t with hP
  set x0 := σ.get ⟨t, ht⟩ with hx0
  have hMi_card_le : Mi.card ≤ k := by
    obtain ⟨s, hs⟩ := (lawAfter k V (σ.take i)).support_nonempty
    obtain ⟨h1, -, -, h4⟩ := aux_sfp_invA k hk V hV _ s hs
    have : s.marked = Mi := h1
    rw [← this]
    exact h4
  have hMi_card : Mi.card = k := by
    have := Finset.card_insert_le (σ.get ⟨i, hi_lt⟩) Mi
    omega
  have hit' : i < t := by
    rcases Nat.lt_or_ge i t with h | h
    · exact h
    · exfalso
      obtain rfl : t = i := le_antisymm h hit
      rw [Finset.insert_eq_of_mem hstale] at hiph
      omega
  have hmarks : ∀ j, i + 1 + j ≤ t →
      marksAt k V σ (i + 1 + j) = phaseRequested σ i (i + 1 + j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.add_zero, aux_sfp_marksAt_succ k V σ i hi_lt,
        aux_sfp_phaseReq_succ σ i i le_rfl hi_lt, aux_sfp_phaseReq_self]
      unfold marksAfter
      rw [if_pos hiph]
      simp
    | succ j ih =>
      intro hj
      have hu : i + 1 + j < σ.length := by omega
      have hnp := hno (i + 1 + j) (by omega) (by omega)
      rw [show i + 1 + (j+1) = (i + 1 + j) + 1 by omega, aux_sfp_marksAt_succ k V σ _ hu,
        aux_sfp_phaseReq_succ σ i _ (by omega) hu]
      unfold marksAfter
      rw [if_neg, ih (by omega)]
      intro hc
      exact hnp ⟨hu, hc⟩
  have hmT : marksAt k V σ t = P := by
    have := hmarks (t - i - 1) (by omega)
    rwa [show i + 1 + (t - i - 1) = t by omega] at this
  set L := (σ.drop i).take (t - i) with hL
  have hlaw : lawAfter k V (σ.take t) =
      L.foldl (fun p r => p.bind (fun s => step k s r)) (lawAfter k V (σ.take i)) := by
    rw [← aux_sfp_law_append, hL, ← List.take_add]
    congr 2
    omega
  have hsupp_i : ∀ s ∈ (lawAfter k V (σ.take i)).support, s.covered = Mi ∧ s.marked = Mi := by
    intro s hs
    obtain ⟨h1, h2, h3, -⟩ := aux_sfp_invA k hk V hV _ s hs
    have hm : s.marked = Mi := h1
    refine ⟨?_, hm⟩
    rw [hm] at h2
    exact (Finset.eq_of_subset_of_card_le h2 (by omega)).symm
  have hsupp_t : ∀ s ∈ (lawAfter k V (σ.take t)).support,
      P ⊆ s.covered ∧ s.covered ⊆ Mi ∪ P ∧ s.covered.card = k := by
    intro s hs
    obtain ⟨h1, h2, h3, -⟩ := aux_sfp_invA k hk V hV _ s hs
    have hm : s.marked = P := by
      rw [← hmT]
      exact h1
    refine ⟨hm ▸ h2, ?_, h3⟩
    rw [hlaw] at hs
    exact aux_sfp_invB k L _ Mi (fun s' hs' => (hsupp_i s' hs').1.subset) s hs
  have hinv : ∀ x ∈ Mi \ P, (lawAfter k V (σ.take t)).map (aux_sfp_act (Equiv.swap x x0)) =
      lawAfter k V (σ.take t) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hMi_fix : Mi.map (Equiv.swap x x0).toEmbedding = Mi :=
      aux_sfp_map_swap Mi x x0 hx.1 hstale
    have hlaw_i : (lawAfter k V (σ.take i)).map (aux_sfp_act (Equiv.swap x x0)) =
        lawAfter k V (σ.take i) := by
      apply aux_sfp_map_fix
      intro s hs
      obtain ⟨h1, h2⟩ := hsupp_i s hs
      obtain ⟨c, m⟩ := s
      simp only at h1 h2
      subst h1 h2
      simp only [aux_sfp_act, hMi_fix]
    have hL_fix : L.map (Equiv.swap x x0) = L := by
      refine (List.map_congr_left ?_).trans (List.map_id L)
      intro a ha
      have haP : a ∈ P := List.mem_toFinset.2 ha
      exact Equiv.swap_apply_of_ne_of_ne (fun h => hx.2 (h ▸ haP)) (fun h => hnew (h ▸ haP))
    rw [hlaw, ← aux_sfp_fold_equiv, hlaw_i, hL_fix]
  have heqp : ∀ x ∈ Mi \ P, (lawAfter k V (σ.take t)).toOuterMeasure {s | x ∉ s.covered} =
      faultProb k V (σ.take t) x0 := by
    intro x hx
    unfold faultProb
    conv_rhs => rw [← hinv x hx]
    rw [PMF.toOuterMeasure_map_apply]
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, aux_sfp_act, Finset.mem_map_equiv,
      Equiv.symm_swap, Equiv.swap_apply_right]
  have hsum : ∑ x ∈ Mi \ P, (lawAfter k V (σ.take t)).toOuterMeasure {s | x ∉ s.covered} =
      ((P \ Mi).card : ℝ≥0∞) := by
    simp only [PMF.toOuterMeasure_apply]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    have key : ∀ s, ∑ x ∈ Mi \ P,
        Set.indicator {s : State M | x ∉ s.covered} (lawAfter k V (σ.take t)) s =
        ((P \ Mi).card : ℝ≥0∞) * lawAfter k V (σ.take t) s := by
      intro s
      by_cases hs : s ∈ (lawAfter k V (σ.take t)).support
      · obtain ⟨h1, h2, h3⟩ := hsupp_t s hs
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        have hf : (Mi \ P).filter (fun x => x ∉ s.covered) = Mi \ s.covered := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨a, _⟩, c⟩
            exact ⟨a, c⟩
          · rintro ⟨a, c⟩
            exact ⟨⟨a, fun hp => c (h1 hp)⟩, c⟩
        have hCM : s.covered \ Mi = P \ Mi := by
          ext x
          simp only [Finset.mem_sdiff]
          constructor
          · rintro ⟨a, b⟩
            have := h2 a
            rw [Finset.mem_union] at this
            rcases this with h | h
            · exact absurd h b
            · exact ⟨h, b⟩
          · rintro ⟨a, b⟩
            exact ⟨h1 a, b⟩
        have e1 := Finset.card_sdiff_add_card_inter Mi s.covered
        have e2 := Finset.card_sdiff_add_card_inter s.covered Mi
        rw [Finset.inter_comm] at e2
        rw [hCM] at e2
        have hc : ((Mi \ P).filter (fun x => x ∉ s.covered)).card = (P \ Mi).card := by
          rw [hf]
          omega
        rw [hc]
      · have h0 := (PMF.apply_eq_zero_iff _ _).2 hs
        simp [Set.indicator_apply, h0]
    simp_rw [key]
    rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  have hx0S : x0 ∈ Mi \ P := Finset.mem_sdiff.2 ⟨hstale, hnew⟩
  have hsum2 : ∑ x ∈ Mi \ P, (lawAfter k V (σ.take t)).toOuterMeasure {s | x ∉ s.covered} =
      ((Mi \ P).card : ℝ≥0∞) * faultProb k V (σ.take t) x0 := by
    rw [Finset.sum_congr rfl heqp, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.eq_div_iff, ← hsum2, hsum]
  · exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hx0S)
  · exact ENNReal.natCast_ne_top _
