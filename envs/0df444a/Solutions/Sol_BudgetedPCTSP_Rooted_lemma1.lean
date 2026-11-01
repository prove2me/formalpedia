-- Prove2me | solution 1 for BudgetedPCTSP.Rooted.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:02:34.550978+00:00
-- url     : https://prove2.me/submissions/6885979a-98c7-46ce-a6ce-241096c4129b

import Mathlib
import Definitions.Def_BudgetedPCTSP_Rooted_Instance
import Definitions.Def_BudgetedPCTSP_Rooted_PDStep

open BudgetedPCTSP.Rooted

variable {V : Type} [Fintype V] [DecidableEq V]

private structure PDInv (I : Instance V) (lam : ℝ) (s : PDState V) : Prop where
  disj : ∀ C₁ ∈ s.comps, ∀ C₂ ∈ s.comps, C₁ ≠ C₂ → Disjoint C₁ C₂
  cover : ∀ v : V, ∃ C ∈ s.comps, v ∈ C
  act_sub : s.active ⊆ s.comps
  comp_ne : ∀ C ∈ s.comps, C.Nonempty
  y_nn : ∀ S : Finset V, 0 ≤ s.y S
  y_supp : ∀ T : Finset V, s.y T ≠ 0 → T.Nonempty ∧ ∃ C ∈ s.comps, T ⊆ C
  edge_le : ∀ e ∈ I.G.edgeSet, edgeLoad s.y e ≤ lam * I.c e
  all_load : ∀ S : Finset V, ∑ T ∈ S.powerset, s.y T ≤ (S.card : ℝ) / 2

private lemma pdInv_init (I : Instance V) (lam : ℝ) (hlam : 0 ≤ lam) :
    PDInv I lam (PDState.init : PDState V) where
  disj C₁ hC₁ C₂ hC₂ hne := by
    rcases Finset.mem_image.mp hC₁ with ⟨i₁, _, rfl⟩
    rcases Finset.mem_image.mp hC₂ with ⟨i₂, _, rfl⟩
    exact Finset.disjoint_singleton.mpr (fun h => hne (by rw [h]))
  cover v := ⟨{v}, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, Finset.mem_singleton_self v⟩
  act_sub := Finset.Subset.rfl
  comp_ne C hC := by
    rcases Finset.mem_image.mp hC with ⟨v, _, rfl⟩
    exact Finset.singleton_nonempty v
  y_nn _ := le_rfl
  y_supp T hT := (hT rfl).elim
  edge_le e he := by
    have hc : 0 ≤ I.c e := I.c_nonneg e he
    have : edgeLoad (PDState.init : PDState V).y e = 0 := by
      unfold edgeLoad PDState.init; simp
    rw [this]; positivity
  all_load S := by
    have : ∑ T ∈ S.powerset, (PDState.init : PDState V).y T = 0 := by
      unfold PDState.init; simp
    rw [this]; positivity

private lemma mem_comp_eq {I : Instance V} {lam : ℝ} {s : PDState V}
    (h : PDInv I lam s) {C₁ C₂ : Finset V} (hC₁ : C₁ ∈ s.comps) (hC₂ : C₂ ∈ s.comps)
    {v : V} (hv₁ : v ∈ C₁) (hv₂ : v ∈ C₂) : C₁ = C₂ := by
  by_contra hne
  exact Finset.disjoint_left.mp (h.disj C₁ hC₁ C₂ hC₂ hne) hv₁ hv₂

private lemma raise_y_nn {I : Instance V} {lam : ℝ} {s : PDState V}
    (h : PDInv I lam s) {Δ : ℝ} (hΔ : 0 ≤ Δ) (S : Finset V) :
    0 ≤ raise s Δ S := by
  unfold raise
  split_ifs <;> linarith [h.y_nn S]

private lemma sum_le_sum_of_ne_zero_real {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (h : ∀ x ∈ s, f x ≠ 0 → x ∈ t) (hf : ∀ x ∈ t, 0 ≤ f x) :
    ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  have h1 : ∑ x ∈ s, f x = ∑ x ∈ s ∩ t, f x := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro x hxs hxnot
    by_contra hne0
    exact hxnot (Finset.mem_inter.mpr ⟨hxs, h x hxs hne0⟩)
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun x hxt _ => hf x hxt)

private lemma sum_union_le_real {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter]
  have : 0 ≤ ∑ x ∈ s ∩ t, f x := Finset.sum_nonneg (fun x _ => hf x)
  linarith

private lemma sum_biUnion_le_real {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) {f : β → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hu := sum_union_le_real (s := t a) (t := s.biUnion t) hf
    linarith

private lemma sum_div_two {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (∑ a ∈ s, (f a : ℝ) / 2) = ((∑ a ∈ s, f a : ℕ) : ℝ) / 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
    push_cast
    ring

private lemma raise_y_supp {I : Instance V} {lam : ℝ} {s : PDState V}
    (h : PDInv I lam s) {Δ : ℝ} (T : Finset V) (hT : raise s Δ T ≠ 0) :
    T.Nonempty ∧ ∃ C ∈ s.comps, T ⊆ C := by
  unfold raise at hT
  by_cases hact : T ∈ s.active
  · have hcomp : T ∈ s.comps := h.act_sub hact
    exact ⟨h.comp_ne T hcomp, T, hcomp, Finset.Subset.rfl⟩
  · rw [if_neg hact, add_zero] at hT
    exact h.y_supp T hT

private lemma raise_edge_le {I : Instance V} {lam : ℝ} {s : PDState V}
    (h : PDInv I lam s) {Δ : ℝ} (hΔ_nn : 0 ≤ Δ) (hnext : IsNextEventTime I lam s Δ)
    (e : Sym2 V) (he : e ∈ I.G.edgeSet) :
    edgeLoad (raise s Δ) e ≤ lam * I.c e := by
  induction e using Sym2.ind with
  | _ u v =>
  have hadj : I.G.Adj u v := I.G.mem_edgeSet.mp he
  rcases h.cover u with ⟨C₁, hC₁, hu₁⟩
  rcases h.cover v with ⟨C₂, hC₂, hv₂⟩
  open Classical in
  have hload_split : edgeLoad (raise s Δ) s(u, v) =
      edgeLoad s.y s(u, v) +
      ∑ A ∈ (Finset.univ : Finset (Finset V)).filter (fun A => Crosses A s(u, v)),
        (if A ∈ s.active then Δ else 0) := by
    unfold edgeLoad raise
    exact Finset.sum_add_distrib
  rw [hload_split]
  have hcross_act : ∀ A : Finset V, Crosses A s(u, v) → A ∈ s.active →
      (A = C₁ ∨ A = C₂) ∧ C₁ ≠ C₂ := by
    rintro A ⟨x, hxA, y, hyA, heq⟩ hA_act
    have hA_comp : A ∈ s.comps := h.act_sub hA_act
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hAC₁ : A = C₁ := mem_comp_eq h hA_comp hC₁ hxA hu₁
      subst hAC₁
      exact ⟨Or.inl rfl, fun h12 => hyA (h12 ▸ hv₂)⟩
    · have hAC₂ : A = C₂ := mem_comp_eq h hA_comp hC₂ hxA hv₂
      subst hAC₂
      exact ⟨Or.inr rfl, fun h12 => hyA (h12.symm ▸ hu₁)⟩
  by_cases hcand_cond : C₁ ≠ C₂ ∧ (C₁ ∈ s.active ∨ C₂ ∈ s.active)
  · rcases hcand_cond with ⟨hne12, hact12⟩
    have hcand : IsEdgeCandidate I s C₁ C₂ u v :=
      ⟨hadj, hC₁, hC₂, hu₁, hv₂, hne12, hact12⟩
    have hΔ_edge : Δ ≤ edgeTime I lam s C₁ C₂ u v := hnext.2 C₁ C₂ u v hcand
    open Classical in
    have hsum_le : (∑ A ∈ (Finset.univ : Finset (Finset V)).filter (fun A => Crosses A s(u, v)),
        (if A ∈ s.active then Δ else 0)) ≤
        ∑ A ∈ ({C₁, C₂} : Finset (Finset V)), (if A ∈ s.active then Δ else 0) := by
      apply sum_le_sum_of_ne_zero_real
      · intro A hA hne0
        rw [Finset.mem_filter] at hA
        have hA_act : A ∈ s.active := by
          by_contra hnot
          exact hne0 (if_neg hnot)
        rcases (hcross_act A hA.2 hA_act).1 with rfl | rfl <;> simp
      · intro A _
        split_ifs <;> linarith
    open Classical in
    have hpair : (∑ A ∈ ({C₁, C₂} : Finset (Finset V)), (if A ∈ s.active then Δ else 0)) =
        (activeCount s C₁ C₂ : ℝ) * Δ := by
      rw [Finset.sum_pair hne12]
      unfold activeCount
      push_cast
      split_ifs <;> ring
    have hcnt_pos : (0 : ℝ) < activeCount s C₁ C₂ := by
      unfold activeCount
      rcases hact12 with h1 | h2
      · rw [if_pos h1]; split_ifs <;> norm_num
      · rw [if_pos h2]; split_ifs <;> norm_num
    unfold edgeTime at hΔ_edge
    have hmul : (activeCount s C₁ C₂ : ℝ) * Δ ≤ lam * I.c s(u, v) - edgeLoad s.y s(u, v) := by
      rw [mul_comm]
      exact (le_div_iff₀ hcnt_pos).mp hΔ_edge
    linarith
  · open Classical in
    have hsum_zero : (∑ A ∈ (Finset.univ : Finset (Finset V)).filter (fun A => Crosses A s(u, v)),
        (if A ∈ s.active then Δ else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      rw [Finset.mem_filter] at hA
      by_cases hA_act : A ∈ s.active
      · exfalso
        apply hcand_cond
        rcases hcross_act A hA.2 hA_act with ⟨rfl | rfl, hne12⟩
        · exact ⟨hne12, Or.inl hA_act⟩
        · exact ⟨hne12, Or.inr hA_act⟩
      · exact if_neg hA_act
    rw [hsum_zero, add_zero]
    exact h.edge_le s(u, v) he

private lemma raise_act_load {I : Instance V} {lam : ℝ} {s : PDState V}
    (h : PDInv I lam s) {Δ : ℝ} (hnext : IsNextEventTime I lam s Δ)
    {A : Finset V} (hA : A ∈ s.active) :
    ∑ T ∈ A.powerset, raise s Δ T ≤ (A.card : ℝ) / 2 := by
  have h1 : ∑ T ∈ A.powerset, raise s Δ T =
      (∑ T ∈ A.powerset, s.y T) + ∑ T ∈ A.powerset, (if T ∈ s.active then Δ else 0) := by
    unfold raise; exact Finset.sum_add_distrib
  have h2 : (∑ T ∈ A.powerset, (if T ∈ s.active then Δ else 0)) = Δ := by
    rw [Finset.sum_eq_single A]
    · exact if_pos hA
    · intro T hT hTA
      have hnot : T ∉ s.active := by
        intro hT_act
        have hT_comp : T ∈ s.comps := h.act_sub hT_act
        have hA_comp : A ∈ s.comps := h.act_sub hA
        rcases h.comp_ne T hT_comp with ⟨x, hx⟩
        have hxA : x ∈ A := Finset.mem_powerset.mp hT hx
        exact hTA (mem_comp_eq h hT_comp hA_comp hx hxA)
      exact if_neg hnot
    · intro hnot
      exact (hnot (Finset.mem_powerset.mpr Finset.Subset.rfl)).elim
  have h3 := hnext.1 A hA
  unfold neutralTime at h3
  linarith

private lemma raise_all_load {I : Instance V} {lam : ℝ} {s : PDState V}
    (h : PDInv I lam s) {Δ : ℝ} (hΔ_nn : 0 ≤ Δ) (hnext : IsNextEventTime I lam s Δ)
    (S : Finset V) :
    ∑ T ∈ S.powerset, raise s Δ T ≤ (S.card : ℝ) / 2 := by
  set Act_S := s.active.filter (fun A => A ⊆ S)
  set U := Act_S.biUnion id
  set R := S \ U
  have hU_sub : U ⊆ S := Finset.biUnion_subset.mpr (fun A hA => (Finset.mem_filter.mp hA).2)
  have hAct_disj : (Act_S : Set (Finset V)).PairwiseDisjoint id := by
    intro A₁ hA₁ A₂ hA₂ hne
    exact h.disj A₁ (h.act_sub (Finset.mem_filter.mp hA₁).1)
      A₂ (h.act_sub (Finset.mem_filter.mp hA₂).1) hne
  have hcard_U : U.card = ∑ A ∈ Act_S, A.card := Finset.card_biUnion hAct_disj
  have hcard_S : S.card = R.card + U.card := (Finset.card_sdiff_add_card_eq_card hU_sub).symm
  have hR_load : ∑ T ∈ R.powerset, raise s Δ T ≤ (R.card : ℝ) / 2 := by
    have heq : ∑ T ∈ R.powerset, raise s Δ T = ∑ T ∈ R.powerset, s.y T := by
      apply Finset.sum_congr rfl
      intro T hT
      have hTR : T ⊆ R := Finset.mem_powerset.mp hT
      have hnot : T ∉ s.active := by
        intro hT_act
        have hTS : T ⊆ S := Finset.Subset.trans hTR Finset.sdiff_subset
        have hT_Act : T ∈ Act_S := Finset.mem_filter.mpr ⟨hT_act, hTS⟩
        have hTU : T ⊆ U := Finset.subset_biUnion_of_mem id hT_Act
        rcases h.comp_ne T (h.act_sub hT_act) with ⟨x, hx⟩
        exact (Finset.mem_sdiff.mp (hTR hx)).2 (hTU hx)
      unfold raise
      rw [if_neg hnot, add_zero]
    rw [heq]
    exact h.all_load R
  have hsum_sub : ∑ T ∈ S.powerset, raise s Δ T ≤
      ∑ T ∈ Act_S.biUnion Finset.powerset ∪ R.powerset, raise s Δ T := by
    apply sum_le_sum_of_ne_zero_real
    · intro T hT hne0
      rcases raise_y_supp h T hne0 with ⟨_, C, hC, hTC⟩
      rw [Finset.mem_union]
      by_cases hC_Act : C ∈ Act_S
      · left
        exact Finset.mem_biUnion.mpr ⟨C, hC_Act, Finset.mem_powerset.mpr hTC⟩
      · right
        rw [Finset.mem_powerset]
        intro z hz
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_powerset.mp hT hz, ?_⟩
        intro hzU
        rcases Finset.mem_biUnion.mp hzU with ⟨A, hA, hzA⟩
        have hCA : C = A :=
          mem_comp_eq h hC (h.act_sub (Finset.mem_filter.mp hA).1) (hTC hz) hzA
        exact hC_Act (hCA ▸ hA)
    · intro T _
      exact raise_y_nn h hΔ_nn T
  have hunion_le : ∑ T ∈ Act_S.biUnion Finset.powerset ∪ R.powerset, raise s Δ T ≤
      (∑ T ∈ Act_S.biUnion Finset.powerset, raise s Δ T) + ∑ T ∈ R.powerset, raise s Δ T :=
    sum_union_le_real (fun T => raise_y_nn h hΔ_nn T)
  have hbi_le : ∑ T ∈ Act_S.biUnion Finset.powerset, raise s Δ T ≤
      ∑ A ∈ Act_S, ∑ T ∈ A.powerset, raise s Δ T :=
    sum_biUnion_le_real Act_S Finset.powerset (fun T => raise_y_nn h hΔ_nn T)
  have hAct_sum_le : ∑ A ∈ Act_S, ∑ T ∈ A.powerset, raise s Δ T ≤
      ∑ A ∈ Act_S, ((A.card : ℝ) / 2) := by
    apply Finset.sum_le_sum
    intro A hA
    exact raise_act_load h hnext (Finset.mem_filter.mp hA).1
  have hAct_card : (∑ A ∈ Act_S, ((A.card : ℝ) / 2)) = (U.card : ℝ) / 2 := by
    rw [sum_div_two Act_S Finset.card, ← hcard_U]
  have hcard_S_r : (S.card : ℝ) = (R.card : ℝ) + (U.card : ℝ) := by
    exact_mod_cast hcard_S
  linarith

private lemma pdInv_step {I : Instance V} {lam : ℝ} {s s' : PDState V}
    (h : PDInv I lam s) (hstep : PDStep I lam s s') : PDInv I lam s' := by
  cases hstep with
  | neutral Δ S hnext hS ht =>
    have hΔ_nn : 0 ≤ Δ := by
      rw [← ht]
      unfold neutralTime
      have := h.all_load S
      linarith
    refine
      { disj := h.disj
        cover := h.cover
        act_sub := Finset.Subset.trans (Finset.erase_subset S s.active) h.act_sub
        comp_ne := h.comp_ne
        y_nn := raise_y_nn h hΔ_nn
        y_supp := raise_y_supp h
        edge_le := raise_edge_le h hΔ_nn hnext
        all_load := raise_all_load h hΔ_nn hnext }
  | edge Δ S₁ S₂ u v hnext he ht =>
    rcases he with ⟨hadj, hS₁, hS₂, hu₁, hv₂, hne12, hact12⟩
    have hΔ_nn : 0 ≤ Δ := by
      rw [← ht]
      unfold edgeTime
      have he_in : s(u, v) ∈ I.G.edgeSet := I.G.mem_edgeSet.mpr hadj
      have hload := h.edge_le s(u, v) he_in
      have hcnt_pos : (0 : ℝ) < activeCount s S₁ S₂ := by
        unfold activeCount
        rcases hact12 with h1 | h2
        · rw [if_pos h1]; split_ifs <;> norm_num
        · rw [if_pos h2]; split_ifs <;> norm_num
      exact div_nonneg (by linarith) hcnt_pos.le
    set U := S₁ ∪ S₂
    set R := (s.comps.erase S₁).erase S₂
    have hR_sub : ∀ C ∈ R, C ∈ s.comps ∧ C ≠ S₁ ∧ C ≠ S₂ := by
      intro C hC
      rw [Finset.mem_erase, Finset.mem_erase] at hC
      exact ⟨hC.2.2, hC.2.1, hC.1⟩
    have hR_disj_U : ∀ C ∈ R, Disjoint C U := by
      intro C hC
      rcases hR_sub C hC with ⟨hC_in, hC1, hC2⟩
      exact Finset.disjoint_union_right.mpr
        ⟨h.disj C hC_in S₁ hS₁ hC1, h.disj C hC_in S₂ hS₂ hC2⟩
    refine
      { disj := ?_
        cover := ?_
        act_sub := ?_
        comp_ne := ?_
        y_nn := raise_y_nn h hΔ_nn
        y_supp := ?_
        edge_le := raise_edge_le h hΔ_nn hnext
        all_load := raise_all_load h hΔ_nn hnext }
    · intro C₁ hC₁ C₂ hC₂ hne
      rcases Finset.mem_insert.mp hC₁ with rfl | hC₁R <;>
        rcases Finset.mem_insert.mp hC₂ with rfl | hC₂R
      · exact (hne rfl).elim
      · exact (hR_disj_U C₂ hC₂R).symm
      · exact hR_disj_U C₁ hC₁R
      · exact h.disj C₁ (hR_sub C₁ hC₁R).1 C₂ (hR_sub C₂ hC₂R).1 hne
    · intro w
      rcases h.cover w with ⟨C, hC, hwC⟩
      by_cases hC1 : C = S₁
      · subst hC1
        exact ⟨U, Finset.mem_insert_self U R, Finset.mem_union_left S₂ hwC⟩
      · by_cases hC2 : C = S₂
        · subst hC2
          exact ⟨U, Finset.mem_insert_self U R, Finset.mem_union_right S₁ hwC⟩
        · exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hC2, Finset.mem_erase.mpr ⟨hC1, hC⟩⟩), hwC⟩
    · intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hCR
      · exact Finset.mem_insert_self U R
      · rw [Finset.mem_erase, Finset.mem_erase] at hCR
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hCR.1, Finset.mem_erase.mpr ⟨hCR.2.1, h.act_sub hCR.2.2⟩⟩)
    · intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hCR
      · exact ⟨u, Finset.mem_union_left S₂ hu₁⟩
      · exact h.comp_ne C (hR_sub C hCR).1
    · intro T hT
      rcases raise_y_supp h T hT with ⟨hT_ne, C, hC, hTC⟩
      refine ⟨hT_ne, ?_⟩
      by_cases hC1 : C = S₁
      · subst hC1
        exact ⟨U, Finset.mem_insert_self U R, Finset.Subset.trans hTC Finset.subset_union_left⟩
      · by_cases hC2 : C = S₂
        · subst hC2
          exact ⟨U, Finset.mem_insert_self U R, Finset.Subset.trans hTC Finset.subset_union_right⟩
        · exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hC2, Finset.mem_erase.mpr ⟨hC1, hC⟩⟩), hTC⟩

private lemma pdInv_of_reachable (I : Instance V) (lam : ℝ) (hlam : 0 ≤ lam)
    (s : PDState V) (hs : IsReachable I lam s) : PDInv I lam s := by
  induction hs with
  | refl => exact pdInv_init I lam hlam
  | tail _ hstep ih => exact pdInv_step ih hstep

theorem solution {V : Type} [Fintype V] [DecidableEq V] (I : Instance V) (lam : ℝ)
    (hlam : 0 ≤ lam) (s : PDState V) (hs : IsCompleteRun I lam s) (S : Finset V) :
    2 * ∑ T ∈ S.powerset, s.y T ≤ (S.card : ℝ) := by
  have h := (pdInv_of_reachable I lam hlam s hs.1).all_load S
  linarith
