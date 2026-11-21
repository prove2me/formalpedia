-- Prove2me | solution 1 for BalasAdditive.Convergence.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T05:26:45.036009+00:00
-- url     : https://prove2.me/submissions/935abb15-f0df-491b-b72b-fe208cc573a8

import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence.SoundAux

open BalasAdditive.Convergence
open Classical

/-! ### Basic Combinatorial & Cancellation Helpers -/

private theorem equalityF_nonempty {n m : ℕ} (P : Problem n m) (J X : Finset (Fin n))
    (hhold : relationsHold P J X) (hnonstrict : ¬ relationsStrict P J X) :
    (equalityF P J X).Nonempty := by
  simp only [relationsStrict, not_forall] at hnonstrict
  obtain ⟨i, hslack, hnotlt⟩ := hnonstrict
  have hle := hhold i hslack
  have heq : negativeSum P X i = P.lp.slack J i := le_antisymm hle (not_lt.mp hnotlt)
  have hsum_lt : ∑ j ∈ X, min (P.lp.A i j) 0 < 0 := by
    change negativeSum P X i < 0
    linarith
  have hex : ∃ j ∈ X, min (P.lp.A i j) 0 < 0 := by
    by_contra h
    have hnonneg : (0 : ℝ) ≤ ∑ j ∈ X, min (P.lp.A i j) 0 :=
      Finset.sum_nonneg fun j hj => not_lt.mp fun hlt => h ⟨j, hj, hlt⟩
    linarith
  obtain ⟨j, hjX, hjmin⟩ := hex
  have hjA : P.lp.A i j < 0 := by
    rcases min_cases (P.lp.A i j) 0 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  exact ⟨j, Finset.mem_filter.mpr ⟨hjX, i, hslack, heq, hjA⟩⟩

private theorem equalityF_subset {n m : ℕ} (P : Problem n m) (J X : Finset (Fin n)) :
    equalityF P J X ⊆ X :=
  Finset.filter_subset _ _

private theorem currentC_cancelAt_self {n : ℕ} (cs : List (Finset (Fin n))) (p : ℕ)
    (X : Finset (Fin n)) (hp : p < cs.length) :
    ((cancelAt cs p X)[p]?).getD ∅ = (cs[p]?).getD ∅ ∪ X := by
  simp [cancelAt, List.getElem?_set_self hp, List.getElem?_eq_getElem hp]

private theorem currentC_cancelAt_ne {n : ℕ} (cs : List (Finset (Fin n))) (p q : ℕ)
    (X : Finset (Fin n)) (hne : p ≠ q) :
    ((cancelAt cs p X)[q]?).getD ∅ = (cs[q]?).getD ∅ := by
  simp [cancelAt, List.getElem?_set_ne hne]

private theorem length_cancelAt {n : ℕ} (cs : List (Finset (Fin n))) (p : ℕ)
    (X : Finset (Fin n)) :
    (cancelAt cs p X).length = cs.length := by
  simp [cancelAt]

private theorem subset_cancelAt {n : ℕ} (cs : List (Finset (Fin n))) (p q : ℕ)
    (X : Finset (Fin n)) :
    (cs[q]?).getD ∅ ⊆ ((cancelAt cs p X)[q]?).getD ∅ := by
  by_cases h : p = q
  · subst h
    by_cases hp : p < cs.length
    · rw [currentC_cancelAt_self cs p X hp]
      exact Finset.subset_union_left
    · have hge : cs.length ≤ p := Nat.le_of_not_lt hp
      simp [cancelAt, List.set_eq_of_length_le hge]
  · rw [currentC_cancelAt_ne cs p q X h]

private theorem cancelOldD_spec {n m : ℕ} (P : Problem n m) (σ : State n) :
    (cancelOldD P σ).length = σ.cancelled.length ∧
    (∀ q : ℕ, (σ.cancelled[q]?).getD ∅ ⊆ ((cancelOldD P σ)[q]?).getD ∅) ∧
    (∀ q : ℕ, σ.cancelled.length = σ.history.length →
      ((cancelOldD P σ)[q]?).getD ∅ ⊆ (σ.cancelled[q]?).getD ∅ ∪ oldD P σ q) := by
  unfold cancelOldD
  generalize hks : (Finset.range (σ.history.length - 1)).toList = ks
  have hnodup : ∀ l : List ℕ, l.Nodup → (∀ k ∈ l, k < σ.history.length - 1) →
      ∀ cs : List (Finset (Fin n)),
      (l.foldl (fun cs k => cancelAt cs k (oldD P σ k)) cs).length = cs.length ∧
      (∀ q : ℕ, (cs[q]?).getD ∅ ⊆
        ((l.foldl (fun cs k => cancelAt cs k (oldD P σ k)) cs)[q]?).getD ∅) ∧
      (∀ q : ℕ, cs.length = σ.history.length →
        ((l.foldl (fun cs k => cancelAt cs k (oldD P σ k)) cs)[q]?).getD ∅ ⊆
          (cs[q]?).getD ∅ ∪
            (if q ∈ l then oldD P σ q else (∅ : Finset (Fin n)))) := by
    intro l hl hlt
    induction l with
    | nil =>
      intro cs
      simp
    | cons k rest ih =>
      obtain ⟨hk_notin, hrest⟩ := List.nodup_cons.mp hl
      have hk_lt : k < σ.history.length - 1 := hlt k List.mem_cons_self
      have hrest_lt : ∀ x ∈ rest, x < σ.history.length - 1 :=
        fun x hx => hlt x (List.mem_cons_of_mem _ hx)
      intro cs
      set cs' := cancelAt cs k (oldD P σ k)
      have hlen' : cs'.length = cs.length := length_cancelAt cs k _
      obtain ⟨ih1, ih2, ih3⟩ := ih hrest hrest_lt cs'
      refine ⟨ih1.trans hlen', ?_, ?_⟩
      · intro q
        exact (subset_cancelAt cs k q _).trans (ih2 q)
      · intro q hcs
        have hstep := ih3 q (hlen'.trans hcs)
        refine hstep.trans ?_
        by_cases hkq : k = q
        · subst hkq
          have hq_len : k < cs.length := by omega
          have hcs'_eq : (cs'[k]?).getD ∅ = (cs[k]?).getD ∅ ∪ oldD P σ k :=
            currentC_cancelAt_self cs k _ hq_len
          simp [hcs'_eq, hk_notin]
        · have hcs'_eq : (cs'[q]?).getD ∅ = (cs[q]?).getD ∅ :=
            currentC_cancelAt_ne cs k q _ hkq
          by_cases hqrest : q ∈ rest <;> simp [hcs'_eq, hqrest, Ne.symm hkq]
  have hks_nodup : ks.Nodup := by
    rw [← hks]
    exact Finset.nodup_toList _
  have hks_lt : ∀ k ∈ ks, k < σ.history.length - 1 := by
    intro k hk
    rw [← hks, Finset.mem_toList, Finset.mem_range] at hk
    exact hk
  obtain ⟨h1, h2, h3⟩ := hnodup ks hks_nodup hks_lt σ.cancelled
  refine ⟨h1, h2, ?_⟩
  intro q hcs
  refine (h3 q hcs).trans ?_
  by_cases hmem : q ∈ ks <;> simp [hmem]

/-! ### Ceiling, Cost, and Slack Inequalities -/

private theorem fold_le {n m : ℕ} (P : Problem n m) (xs : List (Finset (Fin n))) :
    ∀ z : WithTop ℝ,
      xs.foldl (fun z J => if P.lp.Feasible J then min z (↑(P.lp.cost J) : WithTop ℝ) else z) z ≤ z ∧
      (∀ x ∈ xs, P.lp.Feasible x →
        xs.foldl (fun z J => if P.lp.Feasible J then min z (↑(P.lp.cost J) : WithTop ℝ) else z) z
          ≤ (↑(P.lp.cost x) : WithTop ℝ)) := by
  induction xs with
  | nil => intro z; simp
  | cons a t ih =>
    intro z
    simp only [List.foldl_cons]
    set z' := (if P.lp.Feasible a then min z (↑(P.lp.cost a) : WithTop ℝ) else z) with hz'
    obtain ⟨i1, i2⟩ := ih z'
    have hz'le : z' ≤ z := by
      rw [hz']; split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    refine ⟨i1.trans hz'le, ?_⟩
    intro x hx hf
    rcases List.mem_cons.mp hx with rfl | hx
    · refine i1.trans ?_
      rw [hz', if_pos hf]
      exact min_le_right _ _
    · exact i2 x hx hf

private theorem ceiling_le {n m : ℕ} (P : Problem n m) (σ : State n) (q : ℕ)
    (hq : q < σ.history.length) (hf : P.lp.Feasible (σ.J q)) :
    ceiling P σ ≤ (↑(P.lp.cost (σ.J q)) : WithTop ℝ) := by
  have hmem : σ.J q ∈ σ.history.map Record.J := by
    simp only [State.J, List.getElem?_eq_getElem hq, Option.map_some, Option.getD_some]
    exact List.mem_map.mpr ⟨_, List.getElem_mem hq, rfl⟩
  exact (fold_le P _ ⊤).2 _ hmem hf

private theorem ceilingFrom_append_le {n m : ℕ} (P : Problem n m)
    (xs : List (Finset (Fin n))) (J : Finset (Fin n)) :
    ceilingFrom P (xs ++ [J]) ≤ ceilingFrom P xs := by
  unfold ceilingFrom
  rw [List.foldl_append]
  exact (fold_le P [J] _).1

private def Better {n m : ℕ} (P : Problem n m) (σ : State n) (K J : Finset (Fin n)) : Prop :=
  P.lp.Feasible J ∧ K ⊂ J ∧ (↑(P.lp.cost J) : WithTop ℝ) < ceiling P σ

private def Dead {n m : ℕ} (P : Problem n m) (σ : State n) (q : ℕ) : Prop :=
  ¬ ∃ J : Finset (Fin n), Better P σ (σ.J q) J

private theorem better_of_ceil_le {n m : ℕ} (P : Problem n m) {σ τ : State n}
    (hceil : ceiling P τ ≤ ceiling P σ) {K J : Finset (Fin n)} (hb : Better P τ K J) :
    Better P σ K J :=
  ⟨hb.1, hb.2.1, lt_of_lt_of_le hb.2.2 hceil⟩

private theorem dead_of_ceil_le {n m : ℕ} (P : Problem n m) {σ τ : State n} {q : ℕ}
    (hceil : ceiling P τ ≤ ceiling P σ) (hJ : τ.J q = σ.J q) (hd : Dead P σ q) :
    Dead P τ q := by
  rintro ⟨J, hb⟩
  rw [hJ] at hb
  exact hd ⟨J, better_of_ceil_le P hceil hb⟩

private theorem cost_mono {n m : ℕ} (P : Problem n m) {K J : Finset (Fin n)} (h : K ⊆ J) :
    P.lp.cost K ≤ P.lp.cost J :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun j _ _ => P.hc j

private theorem cost_add_subset_sdiff {n m : ℕ} (P : Problem n m) {K J X : Finset (Fin n)}
    (hKJ : K ⊆ J) (hX : X ⊆ J \ K) :
    P.lp.cost K + ∑ j ∈ X, P.lp.c j ≤ P.lp.cost J := by
  have hdisj : Disjoint K X := by
    rw [Finset.disjoint_left]
    intro j hjK hjX
    exact (Finset.mem_sdiff.mp (hX hjX)).2 hjK
  have hunion : K ∪ X ⊆ J :=
    Finset.union_subset hKJ (hX.trans Finset.sdiff_subset)
  calc P.lp.cost K + ∑ j ∈ X, P.lp.c j
      = P.lp.cost (K ∪ X) := by simp [BinaryLP.cost, Finset.sum_union hdisj]
    _ ≤ P.lp.cost J := cost_mono P hunion

private theorem cost_add_mem_sdiff {n m : ℕ} (P : Problem n m) {K J : Finset (Fin n)} {j : Fin n}
    (hKJ : K ⊆ J) (hj : j ∈ J \ K) :
    P.lp.cost K + P.lp.c j ≤ P.lp.cost J := by
  simpa using cost_add_subset_sdiff P hKJ (Finset.singleton_subset_iff.mpr hj)

private theorem not_mem_oldD_of_better {n m : ℕ} (P : Problem n m) {σ : State n} {p : ℕ}
    {J : Finset (Fin n)} (hb : Better P σ (σ.J p) J) {j : Fin n} (hj : j ∈ J \ σ.J p) :
    j ∉ oldD P σ p := by
  intro hmem
  have hceil : ceiling P σ ≤ (↑(P.lp.cost (σ.J p) + P.lp.c j) : WithTop ℝ) :=
    (Finset.mem_filter.mp hmem).2.2
  have hle : (↑(P.lp.cost (σ.J p) + P.lp.c j) : WithTop ℝ) ≤ (↑(P.lp.cost J) : WithTop ℝ) :=
    WithTop.coe_le_coe.mpr (cost_add_mem_sdiff P (le_of_lt hb.2.1) hj)
  exact not_lt_of_ge (hceil.trans hle) hb.2.2

private theorem not_feasible_of_better {n m : ℕ} (P : Problem n m) {σ : State n} {q : ℕ}
    (hq : q < σ.history.length) {J : Finset (Fin n)} (hb : Better P σ (σ.J q) J) :
    ¬ P.lp.Feasible (σ.J q) := by
  intro hfeas
  have h1 : ceiling P σ ≤ (↑(P.lp.cost (σ.J q)) : WithTop ℝ) := ceiling_le P σ q hq hfeas
  have h2 : (↑(P.lp.cost (σ.J q)) : WithTop ℝ) ≤ (↑(P.lp.cost J) : WithTop ℝ) :=
    WithTop.coe_le_coe.mpr (cost_mono P (le_of_lt hb.2.1))
  exact not_lt_of_ge (h1.trans h2) hb.2.2

private theorem better_of_subset_better {n m : ℕ} (P : Problem n m) {σ : State n}
    {K : Finset (Fin n)} {q : ℕ} (hq : q < σ.history.length) {J : Finset (Fin n)}
    (hb : Better P σ K J) (hsub : σ.J q ⊆ J) :
    Better P σ (σ.J q) J := by
  refine ⟨hb.1, ?_, hb.2.2⟩
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsub, ?_⟩
  intro heq
  have hfeas_q : P.lp.Feasible (σ.J q) := heq ▸ hb.1
  have hceil : ceiling P σ ≤ (↑(P.lp.cost (σ.J q)) : WithTop ℝ) := ceiling_le P σ q hq hfeas_q
  rw [heq] at hceil
  exact not_lt_of_ge hceil hb.2.2

private theorem sum_min_zero_nonpos {α : Type} (s : Finset α) (f : α → ℝ) :
    ∑ x ∈ s, min (f x) 0 ≤ 0 := by
  have hnonneg : 0 ≤ ∑ x ∈ s, -min (f x) 0 :=
    Finset.sum_nonneg fun x _ => by
      have := min_le_right (f x) 0
      linarith
  rw [Finset.sum_neg_distrib] at hnonneg
  linarith

private theorem feasible_slack_bound {n m : ℕ} (P : Problem n m) {K J X : Finset (Fin n)}
    (hKJ : K ⊆ J) (hfeas : P.lp.Feasible J) {i : Fin m}
    (hnonneg : ∀ j ∈ (J \ K) \ X, 0 ≤ P.lp.A i j) :
    negativeSum P X i ≤ P.lp.slack K i := by
  have hdisj_K : Disjoint K (J \ K) := by
    rw [Finset.disjoint_left]
    intro x hxK hx
    exact (Finset.mem_sdiff.mp hx).2 hxK
  have hunion_K : K ∪ (J \ K) = J := by
    ext x
    by_cases hx : x ∈ K
    · simp [hx, hKJ hx]
    · simp [hx]
  have hslack_le : ∑ j ∈ J \ K, P.lp.A i j ≤ P.lp.slack K i := by
    have hf := hfeas i
    unfold BinaryLP.slack at hf ⊢
    rw [← hunion_K, Finset.sum_union hdisj_K] at hf
    linarith
  have hdisj_JK : Disjoint ((J \ K) ∩ X) ((J \ K) \ X) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).2
  have hunion_JK : ((J \ K) ∩ X) ∪ ((J \ K) \ X) = J \ K := by
    ext x
    by_cases hx : x ∈ X <;> simp [hx]
  have hsum_JK : ∑ j ∈ J \ K, P.lp.A i j =
      ∑ j ∈ (J \ K) ∩ X, P.lp.A i j + ∑ j ∈ (J \ K) \ X, P.lp.A i j := by
    rw [← Finset.sum_union hdisj_JK, hunion_JK]
  have hrest_nonneg : 0 ≤ ∑ j ∈ (J \ K) \ X, P.lp.A i j :=
    Finset.sum_nonneg hnonneg
  have hinter_le : ∑ j ∈ (J \ K) ∩ X, min (P.lp.A i j) 0 ≤ ∑ j ∈ (J \ K) ∩ X, P.lp.A i j :=
    Finset.sum_le_sum fun j _ => min_le_left (P.lp.A i j) 0
  have hdisj_X : Disjoint ((J \ K) ∩ X) (X \ (J \ K)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).1
  have hunion_X : ((J \ K) ∩ X) ∪ (X \ (J \ K)) = X := by
    ext x
    by_cases hx1 : x ∈ J \ K <;> by_cases hx2 : x ∈ X <;> simp [hx1, hx2]
  have hsum_X : negativeSum P X i =
      ∑ j ∈ (J \ K) ∩ X, min (P.lp.A i j) 0 + ∑ j ∈ X \ (J \ K), min (P.lp.A i j) 0 := by
    unfold negativeSum
    rw [← Finset.sum_union hdisj_X, hunion_X]
  have hextra_nonpos : ∑ j ∈ X \ (J \ K), min (P.lp.A i j) 0 ≤ 0 :=
    sum_min_zero_nonpos _ _
  linarith

private theorem equalityF_subset_sdiff {n m : ℕ} (P : Problem n m) {K J X : Finset (Fin n)}
    (hKJ : K ⊆ J) (hfeas : P.lp.Feasible J)
    (hnonneg : ∀ j ∈ (J \ K) \ X, ∀ i : Fin m, P.lp.slack K i < 0 → 0 ≤ P.lp.A i j) :
    equalityF P K X ⊆ J \ K := by
  intro j₀ hj₀
  obtain ⟨hj₀X, i, hslack, heq, hj₀A⟩ := Finset.mem_filter.mp hj₀
  by_contra hj₀_not
  have hj₀_diff : j₀ ∈ X \ (J \ K) := Finset.mem_sdiff.mpr ⟨hj₀X, hj₀_not⟩
  have hdisj_K : Disjoint K (J \ K) := by
    rw [Finset.disjoint_left]
    intro x hxK hx
    exact (Finset.mem_sdiff.mp hx).2 hxK
  have hunion_K : K ∪ (J \ K) = J := by
    ext x
    by_cases hx : x ∈ K
    · simp [hx, hKJ hx]
    · simp [hx]
  have hslack_le : ∑ j ∈ J \ K, P.lp.A i j ≤ P.lp.slack K i := by
    have hf := hfeas i
    unfold BinaryLP.slack at hf ⊢
    rw [← hunion_K, Finset.sum_union hdisj_K] at hf
    linarith
  have hdisj_JK : Disjoint ((J \ K) ∩ X) ((J \ K) \ X) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).2
  have hunion_JK : ((J \ K) ∩ X) ∪ ((J \ K) \ X) = J \ K := by
    ext x
    by_cases hx : x ∈ X <;> simp [hx]
  have hsum_JK : ∑ j ∈ J \ K, P.lp.A i j =
      ∑ j ∈ (J \ K) ∩ X, P.lp.A i j + ∑ j ∈ (J \ K) \ X, P.lp.A i j := by
    rw [← Finset.sum_union hdisj_JK, hunion_JK]
  have hrest_nonneg : 0 ≤ ∑ j ∈ (J \ K) \ X, P.lp.A i j :=
    Finset.sum_nonneg fun j hj => hnonneg j hj i hslack
  have hinter_le : ∑ j ∈ (J \ K) ∩ X, min (P.lp.A i j) 0 ≤ ∑ j ∈ (J \ K) ∩ X, P.lp.A i j :=
    Finset.sum_le_sum fun j _ => min_le_left (P.lp.A i j) 0
  have hdisj_X : Disjoint ((J \ K) ∩ X) (X \ (J \ K)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).1
  have hunion_X : ((J \ K) ∩ X) ∪ (X \ (J \ K)) = X := by
    ext x
    by_cases hx1 : x ∈ J \ K <;> by_cases hx2 : x ∈ X <;> simp [hx1, hx2]
  have hsum_X : negativeSum P X i =
      ∑ j ∈ (J \ K) ∩ X, min (P.lp.A i j) 0 + ∑ j ∈ X \ (J \ K), min (P.lp.A i j) 0 := by
    unfold negativeSum
    rw [← Finset.sum_union hdisj_X, hunion_X]
  have herase := Finset.add_sum_erase (X \ (J \ K)) (fun j => min (P.lp.A i j) 0) hj₀_diff
  have hj₀_min : min (P.lp.A i j₀) 0 = P.lp.A i j₀ := min_eq_left (le_of_lt hj₀A)
  have herase_nonpos : ∑ j ∈ (X \ (J \ K)).erase j₀, min (P.lp.A i j) 0 ≤ 0 :=
    sum_min_zero_nonpos _ _
  linarith

/-! ### Search-Tree Structure and Ancestor Linearity -/

private inductive Anc (par : ℕ → ℕ) (u : ℕ) : ℕ → Prop where
  | refl : Anc par u u
  | step {v : ℕ} (hv : 0 < v) (h : Anc par u (par v)) : Anc par u v

private theorem anc_le {par : ℕ → ℕ} (hpar : ∀ q > 0, par q < q) {u v : ℕ}
    (h : Anc par u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | @step v hv _ ih => exact ih.trans (Nat.le_of_lt (hpar v hv))

private theorem anc_trans {par : ℕ → ℕ} {a b c : ℕ}
    (h1 : Anc par a b) (h2 : Anc par b c) : Anc par a c := by
  induction h2 with
  | refl => exact h1
  | @step v hv _ ih => exact Anc.step hv ih

private theorem anc_comparable {par : ℕ → ℕ} {a b c : ℕ}
    (h1 : Anc par a c) (h2 : Anc par b c) : Anc par a b ∨ Anc par b a := by
  induction h1 generalizing b with
  | refl => exact Or.inr h2
  | @step v hv hprev ih =>
    cases h2 with
    | refl => exact Or.inl (Anc.step hv hprev)
    | step _ hprev2 => exact ih hprev2

private theorem anc_zero {par : ℕ → ℕ} (hpar : ∀ q > 0, par q < q) :
    ∀ v : ℕ, Anc par 0 v := by
  intro v
  induction v using Nat.strong_induction_on with
  | h v ih =>
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · exact Anc.refl
    · exact Anc.step hv (ih (par v) (hpar v hv))

private theorem anc_first_step {par : ℕ → ℕ} {w u : ℕ}
    (h : Anc par w u) (hne : w ≠ u) :
    ∃ u₁ : ℕ, 0 < u₁ ∧ par u₁ = w ∧ Anc par u₁ u := by
  induction h with
  | refl => exact absurd rfl hne
  | @step v hv _ ih =>
    by_cases hw : w = par v
    · exact ⟨v, hv, hw.symm, Anc.refl⟩
    · obtain ⟨u₁, hu₁_pos, hu₁_par, hu₁_anc⟩ := ih hw
      exact ⟨u₁, hu₁_pos, hu₁_par, Anc.step hv hu₁_anc⟩

private theorem anc_subset_J {n : ℕ} (σ : State n) (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n))
    (hpar : ∀ q > 0, par q < q)
    (hstep : ∀ q, 0 < q → q < σ.history.length → σ.J q = σ.J (par q) ∪ edgeX q)
    {u v : ℕ} (hv : v < σ.history.length) (h : Anc par u v) :
    σ.J u ⊆ σ.J v := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @step w hw _ ih =>
    have hpar_lt : par w < σ.history.length := lt_trans (hpar w hw) hv
    rw [hstep w hw hv]
    exact (ih hpar_lt).trans Finset.subset_union_left

private theorem anc_ssubset_J {n : ℕ} (σ : State n) (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n))
    (hpar : ∀ q > 0, par q < q)
    (hstep : ∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧ (edgeX q).Nonempty ∧ Disjoint (edgeX q) (σ.J (par q)))
    {u v : ℕ} (hv : v < σ.history.length) (h : Anc par u v) (hne : u ≠ v) :
    σ.J u ⊂ σ.J v := by
  cases h with
  | refl => exact absurd rfl hne
  | step hw hprev =>
    have hpar_lt : par v < σ.history.length := lt_trans (hpar v hw) hv
    have hsub : σ.J u ⊆ σ.J (par v) :=
      anc_subset_J σ par edgeX hpar (fun q h0 h1 => (hstep q h0 h1).1) hpar_lt hprev
    obtain ⟨heq, ⟨x, hx⟩, hdisj⟩ := hstep v hw hv
    have hss : σ.J (par v) ⊂ σ.J v := by
      rw [heq, Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, ?_⟩
      intro heq'
      have hx_in : x ∈ σ.J (par v) := by
        have : x ∈ σ.J (par v) ∪ edgeX v := Finset.mem_union_right _ hx
        rwa [← heq'] at this
      exact Finset.disjoint_left.mp hdisj hx hx_in
    exact lt_of_le_of_lt hsub hss

private theorem mem_J_origin {n : ℕ} (σ : State n) (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n))
    (hpar : ∀ q > 0, par q < q) (hJ0 : σ.J 0 = ∅)
    (hstep : ∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧ (edgeX q).Nonempty ∧ Disjoint (edgeX q) (σ.J (par q))) :
    ∀ p < σ.history.length, ∀ x ∈ σ.J p,
      ∃ q, 0 < q ∧ q ≤ p ∧ σ.J (par q) ⊂ σ.J p ∧ x ∈ edgeX q := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hp x hx
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · simp [hJ0] at hx
    · obtain ⟨heq, _, _⟩ := hstep p hp0 hp
      have hss_p : σ.J (par p) ⊂ σ.J p :=
        anc_ssubset_J σ par edgeX hpar hstep hp (Anc.step hp0 Anc.refl)
          (Nat.ne_of_lt (hpar p hp0))
      rw [heq] at hx
      rcases Finset.mem_union.mp hx with hx_par | hx_edge
      · have hpar_lt : par p < p := hpar p hp0
        obtain ⟨q, hq0, hqle, hss, hxq⟩ := ih (par p) hpar_lt (lt_trans hpar_lt hp) x hx_par
        exact ⟨q, hq0, hqle.trans (Nat.le_of_lt hpar_lt), hss.trans hss_p, hxq⟩
      · exact ⟨p, hp0, le_rfl, hss_p, hx_edge⟩

private theorem not_mem_of_sibling_lt {n : ℕ} (σ : State n)
    (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n))
    (hpar : ∀ q > 0, par q < q)
    (htree : ∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧
      (edgeX q).Nonempty ∧
      edgeX q ⊆ σ.N (par q) ∧
      Disjoint (edgeX q) (σ.J (par q)) ∧
      edgeX q ⊆ σ.currentC (par q) ∧
      (∀ r, q ≤ r → r < σ.history.length →
        σ.J (par q) ⊂ σ.J r → Disjoint (σ.N r) (edgeX q)) ∧
      (∀ r, q < r → r < σ.history.length →
        par r = par q → Disjoint (edgeX r) (edgeX q)))
    {u₁ v₁ z : ℕ} (hu₁_pos : 0 < u₁) (hv₁_pos : 0 < v₁) (hu₁v₁ : u₁ < v₁)
    (hpar_eq : par v₁ = par u₁) (hz_len : z < σ.history.length)
    (hanc : Anc par v₁ z) {x : Fin n} (hx : x ∈ edgeX u₁) :
    x ∉ σ.J z := by
  have hstep_basic : ∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧ (edgeX q).Nonempty ∧ Disjoint (edgeX q) (σ.J (par q)) :=
    fun q h0 h1 => ⟨(htree q h0 h1).1, (htree q h0 h1).2.1, (htree q h0 h1).2.2.2.1⟩
  have hu₁_len : u₁ < σ.history.length :=
    lt_of_lt_of_le hu₁v₁ (le_trans (anc_le hpar hanc) (Nat.le_of_lt hz_len))
  obtain ⟨_, _, _, hdisj_u₁_J, _, hdisj_N, hdisj_sib⟩ := htree u₁ hu₁_pos hu₁_len
  induction hanc with
  | refl =>
    obtain ⟨hJv₁, _, _⟩ := htree v₁ hv₁_pos hz_len
    rw [hJv₁, hpar_eq, Finset.mem_union, not_or]
    refine ⟨Finset.disjoint_left.mp hdisj_u₁_J hx, ?_⟩
    exact Finset.disjoint_right.mp (hdisj_sib v₁ hu₁v₁ hz_len hpar_eq) hx
  | @step z' hz'_pos hprev ih =>
    have hpar_z'_lt : par z' < σ.history.length := lt_trans (hpar z' hz'_pos) hz_len
    have hx_not_par : x ∉ σ.J (par z') := ih hpar_z'_lt
    obtain ⟨hJz', _, hedge_sub_N, _, _, _, _⟩ := htree z' hz'_pos hz_len
    rw [hJz', Finset.mem_union, not_or]
    refine ⟨hx_not_par, ?_⟩
    have hv₁_le_par : v₁ ≤ par z' := anc_le hpar hprev
    have hu₁_le_par : u₁ ≤ par z' := Nat.le_of_lt (lt_of_lt_of_le hu₁v₁ hv₁_le_par)
    have hss_v₁ : σ.J (par v₁) ⊂ σ.J v₁ :=
      anc_ssubset_J σ par edgeX hpar hstep_basic (lt_of_le_of_lt hv₁_le_par hpar_z'_lt)
        (Anc.step hv₁_pos Anc.refl) (Nat.ne_of_lt (hpar v₁ hv₁_pos))
    have hsub_par : σ.J v₁ ⊆ σ.J (par z') :=
      anc_subset_J σ par edgeX hpar (fun q h0 h1 => (hstep_basic q h0 h1).1) hpar_z'_lt hprev
    have hss_par : σ.J (par u₁) ⊂ σ.J (par z') := by
      rw [← hpar_eq]
      exact lt_of_lt_of_le hss_v₁ hsub_par
    have hdisj := hdisj_N (par z') hu₁_le_par hpar_z'_lt hss_par
    intro hx_edge
    exact Finset.disjoint_left.mp hdisj (hedge_sub_N hx_edge) hx

private structure TreeInv {n m : ℕ} (P : Problem n m) (σ : State n) : Prop where
  hlen_pos : 0 < σ.history.length
  hcanc_len : σ.cancelled.length = σ.history.length
  hJ0 : σ.J 0 = ∅
  hsnap_sub : ∀ q < σ.history.length, σ.snapshotC q ⊆ σ.currentC q
  hphase_start : σ.phase = .start →
    (∀ q < σ.history.length, σ.currentC q = σ.snapshotC q) ∧
    σ.currentC (σ.history.length - 1) = ∅
  hphase_scan : ∀ bound, σ.phase = .scan bound →
    bound ≤ σ.history.length - 1 ∧
    ∀ q < bound, σ.currentC q ⊆ σ.snapshotC q ∪ oldD P σ q
  tree : ∃ (par : ℕ → ℕ) (edgeX : ℕ → Finset (Fin n)),
    (∀ q > 0, par q < q) ∧
    (∀ q, 0 < q → q < σ.history.length →
      σ.J q = σ.J (par q) ∪ edgeX q ∧
      (edgeX q).Nonempty ∧
      edgeX q ⊆ σ.N (par q) ∧
      Disjoint (edgeX q) (σ.J (par q)) ∧
      edgeX q ⊆ σ.currentC (par q) ∧
      (∀ r, q ≤ r → r < σ.history.length →
        σ.J (par q) ⊂ σ.J r → Disjoint (σ.N r) (edgeX q)) ∧
      (∀ r, q < r → r < σ.history.length →
        par r = par q → Disjoint (edgeX r) (edgeX q))) ∧
    (∀ u₁ v₁, 0 < v₁ → v₁ < u₁ → u₁ < σ.history.length →
      par u₁ = par v₁ → ∀ z, u₁ ≤ z → z < σ.history.length → ¬ Anc par v₁ z) ∧
    (∀ u v, u < v → v < σ.history.length → σ.J u ⊆ σ.J v → Anc par u v)

private theorem treeInv_init {n m : ℕ} (P : Problem n m) : TreeInv P (init P) := by
  refine
    { hlen_pos := by simp [init]
      hcanc_len := by simp [init]
      hJ0 := by simp [init, State.J]
      hsnap_sub := ?_
      hphase_start := ?_
      hphase_scan := by intro bound h; simp [init] at h
      tree := ⟨fun _ => 0, fun _ => ∅, fun q hq => hq,
        fun q hq0 hq1 => by simp [init] at hq1; omega,
        fun u₁ v₁ _ _ hu₁ => by simp [init] at hu₁; omega,
        fun u v _ hv => by simp [init] at hv; omega⟩ }
  · intro q hq
    simp [init] at hq
    subst hq
    simp [init, State.currentC, State.snapshotC]
  · intro _
    refine ⟨?_, by simp [init, State.currentC]⟩
    intro q hq
    simp [init] at hq
    subst hq
    simp [init, State.currentC, State.snapshotC]

private theorem treeInv_appendSolution {n m : ℕ} (P : Problem n m) (σ : State n)
    (hinv : TreeInv P σ) (p : ℕ) (hp : p < σ.history.length) (X : Finset (Fin n))
    (hX_ne : X.Nonempty) (hX_sub : X ⊆ σ.N p) (hX_disj_curr : Disjoint X (σ.currentC p))
    (hp_anc : p = σ.history.length - 1 ∨ σ.J p ⊂ σ.latest) :
    TreeInv P (appendSolution P σ p X X) ∧ Disjoint X (σ.J p) := by
  set τ := appendSolution P σ p X X
  set L := σ.history.length
  obtain ⟨par, edgeX, hpar, htree, hclosed, hchain⟩ := hinv.tree
  have hL_pos : 0 < L := hinv.hlen_pos
  have hstep_basic : ∀ q, 0 < q → q < L →
      σ.J q = σ.J (par q) ∪ edgeX q ∧ (edgeX q).Nonempty ∧ Disjoint (edgeX q) (σ.J (par q)) :=
    fun q h0 h1 => ⟨(htree q h0 h1).1, (htree q h0 h1).2.1, (htree q h0 h1).2.2.2.1⟩
  have hX_disj_Jp : Disjoint X (σ.J p) := by
    rw [Finset.disjoint_left]
    intro x hxX hxJp
    obtain ⟨q, hq0, hqle, hss, hxq⟩ :=
      mem_J_origin σ par edgeX hpar hinv.hJ0 hstep_basic p hp x hxJp
    have hdisj_N : Disjoint (σ.N p) (edgeX q) :=
      (htree q hq0 (lt_of_le_of_lt hqle hp)).2.2.2.2.2.1 p hqle hp hss
    exact Finset.disjoint_left.mp hdisj_N (hX_sub hxX) hxq
  have hp_anc_L1 : Anc par p (L - 1) := by
    rcases hp_anc with rfl | hss_lat
    · exact Anc.refl
    · have hlat_eq : σ.latest = σ.J (L - 1) := rfl
      rw [hlat_eq] at hss_lat
      have hp_ne : p ≠ L - 1 := fun heq => ne_of_ssubset hss_lat (heq ▸ rfl)
      exact hchain p (L - 1) (by omega) (by omega) (le_of_lt hss_lat)
  have hτ_len : τ.history.length = L + 1 := by simp [τ, appendSolution, L]
  have hcs_len : (cancelAt σ.cancelled p X).length = L := by
    rw [length_cancelAt, hinv.hcanc_len]
  have hτ_canc_len : τ.cancelled.length = τ.history.length := by
    simp [τ, appendSolution, hcs_len, L]
  have hτ_J_old : ∀ q < L, τ.J q = σ.J q := by
    intro q hq
    simp [τ, appendSolution, State.J, List.getElem?_append_left hq]
  have hτ_J_new : τ.J L = σ.J p ∪ X := by
    simp [τ, appendSolution, State.J, L]
  have hτ_N_old : ∀ q < L, τ.N q = σ.N q := by
    intro q hq
    simp [τ, appendSolution, State.N, List.getElem?_append_left hq]
  have hτ_N_new : τ.N L = newN P σ.history (cancelAt σ.cancelled p X) (σ.J p ∪ X) := by
    simp [τ, appendSolution, State.N, L]
  have hτ_curr_old : ∀ q < L, τ.currentC q = ((cancelAt σ.cancelled p X)[q]?).getD ∅ := by
    intro q hq
    have hq' : q < (cancelAt σ.cancelled p X).length := by omega
    simp [τ, appendSolution, State.currentC, List.getElem?_append_left hq']
  have hτ_curr_new : τ.currentC L = ∅ := by
    have hL' : L = (cancelAt σ.cancelled p X).length := hcs_len.symm
    simp [τ, appendSolution, State.currentC, hL']
  let par' : ℕ → ℕ := fun q => if q = L then p else if q < L then par q else 0
  let edgeX' : ℕ → Finset (Fin n) := fun q => if q = L then X else edgeX q
  have hpar' : ∀ q > 0, par' q < q := by
    intro q hq
    dsimp [par']
    split_ifs with h1 h2
    · subst h1; exact hp
    · exact hpar q hq
    · exact hq
  have anc_par'_to_par : ∀ {a b : ℕ}, Anc par' a b → b < L → Anc par a b := by
    intro a b h
    induction h with
    | refl => intro _; exact Anc.refl
    | @step w hw _ ih =>
      intro hwL
      have hpar'_w : par' w = par w := by simp [par', Nat.ne_of_lt hwL, hwL]
      have hpar_lt : par w < L := lt_trans (hpar w hw) hwL
      exact Anc.step hw (hpar'_w ▸ ih (hpar'_w.symm ▸ hpar_lt))
  have anc_par_to_par' : ∀ {a b : ℕ}, Anc par a b → b < L → Anc par' a b := by
    intro a b h
    induction h with
    | refl => intro _; exact Anc.refl
    | @step w hw _ ih =>
      intro hwL
      have hpar'_w : par' w = par w := by simp [par', Nat.ne_of_lt hwL, hwL]
      have hpar_lt : par w < L := lt_trans (hpar w hw) hwL
      exact Anc.step hw (hpar'_w.symm ▸ ih hpar_lt)
  have hnewN_disj : ∀ w < L, σ.J w ⊂ σ.J p ∪ X →
      ∀ S : Finset (Fin n), S ⊆ ((cancelAt σ.cancelled p X)[w]?).getD ∅ →
      Disjoint (τ.N L) S := by
    intro w hw hss S hS
    rw [hτ_N_new, Finset.disjoint_left]
    intro j hjN hjS
    have hj_not_inh : j ∉ inheritedC σ.history (cancelAt σ.cancelled p X) (σ.J p ∪ X) :=
      (Finset.mem_filter.mp hjN).2.1
    apply hj_not_inh
    unfold inheritedC
    rw [Finset.mem_biUnion]
    refine ⟨w, Finset.mem_range.mpr hw, ?_⟩
    have hJw : ((σ.history[w]?).map Record.J).getD ∅ = σ.J w := rfl
    rw [hJw, if_pos hss]
    exact hS hjS
  have htree' : ∀ q, 0 < q → q < τ.history.length →
      τ.J q = τ.J (par' q) ∪ edgeX' q ∧
      (edgeX' q).Nonempty ∧
      edgeX' q ⊆ τ.N (par' q) ∧
      Disjoint (edgeX' q) (τ.J (par' q)) ∧
      edgeX' q ⊆ τ.currentC (par' q) ∧
      (∀ r, q ≤ r → r < τ.history.length →
        τ.J (par' q) ⊂ τ.J r → Disjoint (τ.N r) (edgeX' q)) ∧
      (∀ r, q < r → r < τ.history.length →
        par' r = par' q → Disjoint (edgeX' r) (edgeX' q)) := by
    intro q hq0 hq_len
    have hq_le : q ≤ L := by omega
    rcases Nat.lt_or_eq_of_le hq_le with hqL | rfl
    · have hpar_q_lt : par q < L := lt_trans (hpar q hq0) hqL
      have hpar'_q : par' q = par q := by simp [par', Nat.ne_of_lt hqL, hqL]
      have hedgeX'_q : edgeX' q = edgeX q := by simp [edgeX', Nat.ne_of_lt hqL]
      rw [hpar'_q, hedgeX'_q, hτ_J_old q hqL, hτ_J_old (par q) hpar_q_lt, hτ_N_old (par q) hpar_q_lt]
      obtain ⟨h1, h2, hsubN, h3, h4, h5, h6⟩ := htree q hq0 hqL
      refine ⟨h1, h2, hsubN, h3, ?_, ?_, ?_⟩
      · rw [hτ_curr_old (par q) hpar_q_lt]
        exact h4.trans (subset_cancelAt σ.cancelled p (par q) X)
      · intro r hqr hr_len hss_r
        have hr_le : r ≤ L := by omega
        rcases Nat.lt_or_eq_of_le hr_le with hrL | rfl
        · rw [hτ_J_old r hrL] at hss_r
          rw [hτ_N_old r hrL]
          exact h5 r hqr hrL hss_r
        · rw [hτ_J_new] at hss_r
          exact hnewN_disj (par q) hpar_q_lt hss_r (edgeX q)
            (h4.trans (subset_cancelAt σ.cancelled p (par q) X))
      · intro r hqr hr_len hpar_eq
        have hr_le : r ≤ L := by omega
        rcases Nat.lt_or_eq_of_le hr_le with hrL | rfl
        · have hpar'_r : par' r = par r := by simp [par', Nat.ne_of_lt hrL, hrL]
          have hedgeX'_r : edgeX' r = edgeX r := by simp [edgeX', Nat.ne_of_lt hrL]
          rw [hpar'_r] at hpar_eq
          rw [hedgeX'_r]
          exact h6 r hqr hrL hpar_eq
        · have hpar'_L : par' L = p := by simp [par']
          have hedgeX'_L : edgeX' L = X := by simp [edgeX']
          rw [hpar'_L] at hpar_eq
          rw [hedgeX'_L]
          subst hpar_eq
          exact hX_disj_curr.mono_right h4
    · have hpar'_L : par' L = p := by simp [par']
      have hedgeX'_L : edgeX' L = X := by simp [edgeX']
      rw [hpar'_L, hedgeX'_L, hτ_J_new, hτ_J_old p hp, hτ_N_old p hp]
      have hp_canc : p < σ.cancelled.length := hinv.hcanc_len.symm ▸ hp
      have hX_in_cs : X ⊆ ((cancelAt σ.cancelled p X)[p]?).getD ∅ := by
        rw [currentC_cancelAt_self σ.cancelled p X hp_canc]
        exact Finset.subset_union_right
      refine ⟨rfl, hX_ne, hX_sub, hX_disj_Jp, ?_, ?_, ?_⟩
      · rw [hτ_curr_old p hp]
        exact hX_in_cs
      · intro r hLr hr_len hss_r
        have hr_eq : r = L := by omega
        subst hr_eq
        rw [hτ_J_new] at hss_r
        exact hnewN_disj p hp hss_r X hX_in_cs
      · intro r hLr hr_len
        omega
  have hclosed' : ∀ u₁ v₁, 0 < v₁ → v₁ < u₁ → u₁ < τ.history.length →
      par' u₁ = par' v₁ → ∀ z, u₁ ≤ z → z < τ.history.length → ¬ Anc par' v₁ z := by
    intro u₁ v₁ hv₁_pos hv₁u₁ hu₁_len hpar_eq z hu₁z hz_len hanc_z
    have hv₁_lt : v₁ < L := by omega
    have hpar'_v₁ : par' v₁ = par v₁ := by simp [par', Nat.ne_of_lt hv₁_lt, hv₁_lt]
    have hu₁_le : u₁ ≤ L := by omega
    rcases Nat.lt_or_eq_of_le hu₁_le with hu₁L | rfl
    · have hpar'_u₁ : par' u₁ = par u₁ := by simp [par', Nat.ne_of_lt hu₁L, hu₁L]
      have hpar_old : par u₁ = par v₁ := hpar'_u₁.symm.trans (hpar_eq.trans hpar'_v₁)
      have hz_le : z ≤ L := by omega
      rcases Nat.lt_or_eq_of_le hz_le with hzL | rfl
      · exact hclosed u₁ v₁ hv₁_pos hv₁u₁ hu₁L hpar_old z hu₁z hzL
          (anc_par'_to_par hanc_z hzL)
      · cases hanc_z with
        | refl => omega
        | step _ hprev =>
          have hprev_p : Anc par v₁ p :=
            anc_par'_to_par (by simpa [par'] using hprev) hp
          exact hclosed u₁ v₁ hv₁_pos hv₁u₁ hu₁L hpar_old (L - 1) (by omega) (by omega)
            (anc_trans hprev_p hp_anc_L1)
    · have hz_eq : z = L := by omega
      subst hz_eq
      have hp_eq : p = par v₁ := by simpa [par', hpar'_v₁] using hpar_eq
      cases hanc_z with
      | refl => omega
      | step _ hprev =>
        have hprev_p : Anc par v₁ p :=
          anc_par'_to_par (by simpa [par'] using hprev) hp
        have hv₁_le_p : v₁ ≤ p := anc_le hpar hprev_p
        have hpar_lt_v₁ : par v₁ < v₁ := hpar v₁ hv₁_pos
        omega
  have hchain' : ∀ u v, u < v → v < τ.history.length → τ.J u ⊆ τ.J v → Anc par' u v := by
    intro u v huv hv_len hsub
    have hv_le : v ≤ L := by omega
    rcases Nat.lt_or_eq_of_le hv_le with hvL | rfl
    · have huL : u < L := lt_trans huv hvL
      rw [hτ_J_old u huL, hτ_J_old v hvL] at hsub
      exact anc_par_to_par' (hchain u v huv hvL hsub) hvL
    · rw [hτ_J_old u huv, hτ_J_new] at hsub
      by_cases hanc_up : Anc par u p
      · exact Anc.step hL_pos (by simpa [par'] using anc_par_to_par' hanc_up hp)
      · exfalso
        by_cases hanc_pu : Anc par p u
        · have hpu_ne : p ≠ u := fun heq => hanc_up (heq ▸ Anc.refl)
          obtain ⟨u₁, hu₁_pos, hu₁_par, hu₁_anc⟩ := anc_first_step hanc_pu hpu_ne
          have hu₁_lt : u₁ < L := lt_of_le_of_lt (anc_le hpar hu₁_anc) huv
          obtain ⟨hJu₁, ⟨x, hx⟩, _, hdisj_Jp, hx_curr, _, _⟩ := htree u₁ hu₁_pos hu₁_lt
          have hx_in_Ju₁ : x ∈ σ.J u₁ := by rw [hJu₁]; exact Finset.mem_union_right _ hx
          have hx_in_Ju : x ∈ σ.J u :=
            anc_subset_J σ par edgeX hpar (fun q h0 h1 => (htree q h0 h1).1) huv hu₁_anc hx_in_Ju₁
          rcases Finset.mem_union.mp (hsub hx_in_Ju) with hxJp | hxX
          · exact Finset.disjoint_left.mp hdisj_Jp hx (hu₁_par.symm ▸ hxJp)
          · have hx_cp : x ∈ σ.currentC p := hu₁_par ▸ hx_curr hx
            exact Finset.disjoint_left.mp hX_disj_curr hxX hx_cp
        · set S := (Finset.range (L + 1)).filter (fun w => Anc par w u ∧ Anc par w p)
          have hS_ne : S.Nonempty := ⟨0, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Nat.zero_lt_succ L), anc_zero hpar u, anc_zero hpar p⟩⟩
          set w := S.max' hS_ne
          obtain ⟨hw_u, hw_p⟩ := (Finset.mem_filter.mp (S.max'_mem hS_ne)).2
          have hwu_ne : w ≠ u := fun heq => hanc_up (heq ▸ hw_p)
          have hwp_ne : w ≠ p := fun heq => hanc_pu (heq ▸ hw_u)
          obtain ⟨u₁, hu₁_pos, hu₁_par, hu₁_anc⟩ := anc_first_step hw_u hwu_ne
          obtain ⟨p₁, hp₁_pos, hp₁_par, hp₁_anc⟩ := anc_first_step hw_p hwp_ne
          have hu₁_lt : u₁ < L := lt_of_le_of_lt (anc_le hpar hu₁_anc) huv
          have hp₁_lt : p₁ < L := lt_of_le_of_lt (anc_le hpar hp₁_anc) hp
          have hu₁p₁_ne : u₁ ≠ p₁ := by
            intro heq
            have hu₁_in_S : u₁ ∈ S := Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (by omega), hu₁_anc, heq ▸ hp₁_anc⟩
            have hu₁_le_w : u₁ ≤ w := S.le_max' u₁ hu₁_in_S
            have hw_lt_u₁ : w < u₁ := by
              have := hpar u₁ hu₁_pos
              omega
            omega
          rcases lt_or_gt_of_ne hu₁p₁_ne with hlt | hgt
          · obtain ⟨hJu₁, ⟨x, hx⟩, _⟩ := hstep_basic u₁ hu₁_pos hu₁_lt
            have hx_in_Ju₁ : x ∈ σ.J u₁ := by rw [hJu₁]; exact Finset.mem_union_right _ hx
            have hx_in_Ju : x ∈ σ.J u :=
              anc_subset_J σ par edgeX hpar (fun q h0 h1 => (hstep_basic q h0 h1).1) huv hu₁_anc hx_in_Ju₁
            have hpar'_eq : par' p₁ = par' u₁ := by
              simp [par', Nat.ne_of_lt hp₁_lt, hp₁_lt, Nat.ne_of_lt hu₁_lt, hu₁_lt, hp₁_par, hu₁_par]
            have hp₁_anc_L : Anc par' p₁ L :=
              Anc.step hL_pos (by simpa [par'] using anc_par_to_par' hp₁_anc hp)
            have hx_edge' : x ∈ edgeX' u₁ := by simp [edgeX', Nat.ne_of_lt hu₁_lt, hx]
            have hx_not_τJL : x ∉ τ.J L :=
              not_mem_of_sibling_lt τ par' edgeX' hpar' htree' hu₁_pos hp₁_pos hlt
                hpar'_eq (by omega) hp₁_anc_L hx_edge'
            rw [hτ_J_new] at hx_not_τJL
            exact hx_not_τJL (hsub hx_in_Ju)
          · exact hclosed u₁ p₁ hp₁_pos hgt hu₁_lt (hu₁_par.trans hp₁_par.symm)
              (L - 1) (by omega) (by omega) (anc_trans hp₁_anc hp_anc_L1)
  refine ⟨?_, hX_disj_Jp⟩
  refine
    { hlen_pos := by omega
      hcanc_len := hτ_canc_len
      hJ0 := by rw [hτ_J_old 0 hL_pos, hinv.hJ0]
      hsnap_sub := ?_
      hphase_start := ?_
      hphase_scan := by intro bound h; simp [τ, appendSolution] at h
      tree := ⟨par', edgeX', hpar', htree', hclosed', hchain'⟩ }
  · intro q _
    simp [τ, appendSolution, State.currentC, State.snapshotC]
  · intro _
    refine ⟨?_, ?_⟩
    · intro q _
      simp [τ, appendSolution, State.currentC, State.snapshotC]
    · have hlast : τ.history.length - 1 = L := by omega
      rw [hlast]
      exact hτ_curr_new

private theorem treeInv_nonAppend {n m : ℕ} (P : Problem n m) (σ τ : State n)
    (hinv : TreeInv P σ) (hhist : τ.history = σ.history)
    (hcanc_len : τ.cancelled.length = σ.cancelled.length)
    (hcanc_mono : ∀ q, σ.currentC q ⊆ τ.currentC q)
    (hstart : τ.phase ≠ .start)
    (hscan : ∀ bound, τ.phase = .scan bound →
      bound ≤ τ.history.length - 1 ∧
      ∀ q < bound, τ.currentC q ⊆ τ.snapshotC q ∪ oldD P τ q) :
    TreeInv P τ := by
  have hJ : ∀ q, τ.J q = σ.J q := fun q => by simp [State.J, hhist]
  have hN : ∀ q, τ.N q = σ.N q := fun q => by simp [State.N, hhist]
  have hsnap : ∀ q, τ.snapshotC q = σ.snapshotC q := fun q => by simp [State.snapshotC, hhist]
  obtain ⟨par, edgeX, hpar, htree, hclosed, hchain⟩ := hinv.tree
  refine
    { hlen_pos := by rw [hhist]; exact hinv.hlen_pos
      hcanc_len := by rw [hcanc_len, hinv.hcanc_len, hhist]
      hJ0 := by rw [hJ 0, hinv.hJ0]
      hsnap_sub := fun q hq => by
        rw [hhist] at hq
        rw [hsnap q]
        exact (hinv.hsnap_sub q hq).trans (hcanc_mono q)
      hphase_start := fun h => absurd h hstart
      hphase_scan := hscan
      tree := ⟨par, edgeX, hpar, ?_, ?_, ?_⟩ }
  · intro q hq0 hq_len
    rw [hhist] at hq_len
    obtain ⟨h1, h2, hsubN, h3, h4, h5, h6⟩ := htree q hq0 hq_len
    refine ⟨by rw [hJ, hJ]; exact h1, h2, by rw [hN]; exact hsubN,
      by rw [hJ]; exact h3, h4.trans (hcanc_mono _), ?_, ?_⟩
    · intro r hqr hr_len hss
      rw [hhist] at hr_len
      rw [hJ, hJ] at hss
      rw [hN]
      exact h5 r hqr hr_len hss
    · intro r hqr hr_len hpar_eq
      rw [hhist] at hr_len
      exact h6 r hqr hr_len hpar_eq
  · intro u₁ v₁ hv₁_pos hv₁u₁ hu₁_len hpar_eq z hu₁z hz_len
    rw [hhist] at hu₁_len hz_len
    exact hclosed u₁ v₁ hv₁_pos hv₁u₁ hu₁_len hpar_eq z hu₁z hz_len
  · intro u v huv hv_len hsub
    rw [hhist] at hv_len
    rw [hJ, hJ] at hsub
    exact hchain u v huv hv_len hsub

private theorem ssubset_of_both_ssubset_latest {n m : ℕ} (P : Problem n m) (σ : State n)
    (hinv : TreeInv P σ) {q k : ℕ} (hqk : q < k) (hk : k < σ.history.length)
    (hq_lat : σ.J q ⊂ σ.latest) (hk_lat : σ.J k ⊂ σ.latest) :
    σ.J q ⊂ σ.J k := by
  obtain ⟨par, edgeX, hpar, htree, _, hchain⟩ := hinv.tree
  have hL_pos := hinv.hlen_pos
  have hlat : σ.latest = σ.J (σ.history.length - 1) := rfl
  rw [hlat] at hq_lat hk_lat
  have hq_ne : q ≠ σ.history.length - 1 := fun h => ne_of_ssubset hq_lat (h ▸ rfl)
  have hk_ne : k ≠ σ.history.length - 1 := fun h => ne_of_ssubset hk_lat (h ▸ rfl)
  have hanc_q : Anc par q (σ.history.length - 1) :=
    hchain q (σ.history.length - 1) (by omega) (by omega) (le_of_lt hq_lat)
  have hanc_k : Anc par k (σ.history.length - 1) :=
    hchain k (σ.history.length - 1) (by omega) (by omega) (le_of_lt hk_lat)
  rcases anc_comparable hanc_q hanc_k with hqk_anc | hkq_anc
  · exact anc_ssubset_J σ par edgeX hpar
      (fun r h0 h1 => ⟨(htree r h0 h1).1, (htree r h0 h1).2.1, (htree r h0 h1).2.2.2.1⟩)
      hk hqk_anc (Nat.ne_of_lt hqk)
  · exact absurd (anc_le hpar hkq_anc) (not_le.mpr hqk)

/-! ### Joint Soundness Invariant (`SoundInv`) -/

private structure SoundInv {n m : ℕ} (P : Problem n m) (σ : State n) : Prop where
  tree : TreeInv P σ
  invC : ∀ p < σ.history.length, ∀ J, Better P σ (σ.J p) J →
    ∀ x ∈ (J \ σ.J p) ∩ σ.currentC p,
      ∃ q, p < q ∧ q < σ.history.length ∧ x ∈ σ.J q ∧ σ.J q ⊆ J
  invInh : ∀ p < σ.history.length, ∀ J, Better P σ (σ.J p) J →
    ∀ j ∈ J \ σ.J p, j ∉ σ.N p →
      ∀ i : Fin m, P.lp.slack (σ.J p) i < 0 → 0 ≤ P.lp.A i j
  deadStart : σ.phase = .start →
    ∀ q < σ.history.length - 1, ¬ (σ.J q ⊂ σ.latest) → Dead P σ q
  deadScan : ∀ bound, σ.phase = .scan bound →
    (∀ q, bound ≤ q → q < σ.history.length → Dead P σ q) ∧
    (∀ q < bound, ¬ (σ.J q ⊂ σ.latest) → Dead P σ q)
  deadStop : σ.phase = .stopped → ∀ q < σ.history.length, Dead P σ q

private theorem soundInv_init {n m : ℕ} (P : Problem n m) : SoundInv P (init P) := by
  refine
    { tree := treeInv_init P
      invC := ?_
      invInh := ?_
      deadStart := by intro _ q hq; simp [init] at hq
      deadScan := by intro bound h; simp [init] at h
      deadStop := by intro h; simp [init] at h }
  · intro p hp J _ x hx
    simp [init] at hp
    subst hp
    have hcurr : (init P).currentC 0 = ∅ := by simp [init, State.currentC]
    rw [hcurr] at hx
    simp at hx
  · intro p hp J hb j hj hj_notN i hslack
    simp [init] at hp
    subst hp
    have hJ0 : (init P).J 0 = ∅ := rfl
    have hN0 : (init P).N 0 = newN P [] [] ∅ := rfl
    rw [hJ0] at hb hj hslack
    rw [hN0] at hj_notN
    by_contra hnot_ge
    apply hj_notN
    simp only [newN, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by simp [inheritedC], ?_, fun hall => hnot_ge (hall i hslack)⟩
    intro hceil_le
    have hceil_eq : ceilingFrom P ([].map Record.J ++ [∅]) = ceiling P (init P) := rfl
    rw [hceil_eq] at hceil_le
    have hcost_le : (↑(P.lp.cost ∅ + P.lp.c j) : WithTop ℝ) ≤ (↑(P.lp.cost J) : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr (cost_add_mem_sdiff P (Finset.empty_subset J) hj)
    exact not_lt_of_ge (hceil_le.trans hcost_le) hb.2.2

/-- Lemma 1 proved directly from `SoundInv`. -/
private theorem lemma1_of_soundInv {n m : ℕ} (P : Problem n m) {σ : State n}
    (hinv : SoundInv P σ) (hph : σ.phase = .start) {J : Finset (Fin n)}
    (hb : Better P σ σ.latest J) :
    Disjoint (J \ σ.latest) σ.C := by
  rw [Finset.disjoint_left]
  intro x hxJ hxC
  unfold State.C inheritedC at hxC
  rw [Finset.mem_biUnion] at hxC
  obtain ⟨p, hp_range, hxp⟩ := hxC
  have hp_len : p < σ.history.length := Finset.mem_range.mp hp_range
  have hJp_eq : ((σ.history[p]?).map Record.J).getD ∅ = σ.J p := rfl
  rw [hJp_eq] at hxp
  split_ifs at hxp with hss_lat
  · have hsnap_eq : (((σ.history[σ.history.length - 1]?).map Record.snapshot).getD [])[p]?.getD ∅ =
        σ.snapshotC p := rfl
    rw [hsnap_eq, ← (hinv.tree.hphase_start hph).1 p hp_len] at hxp
    have hb_p : Better P σ (σ.J p) J := ⟨hb.1, hss_lat.trans hb.2.1, hb.2.2⟩
    have hx_not_Jp : x ∉ σ.J p := fun h =>
      (Finset.mem_sdiff.mp hxJ).2 (le_of_lt hss_lat h)
    have hx_inter : x ∈ (J \ σ.J p) ∩ σ.currentC p :=
      Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxJ).1, hx_not_Jp⟩, hxp⟩
    obtain ⟨q, hpq, hq_len, hxq, hJq_sub⟩ := hinv.invC p hp_len J hb_p x hx_inter
    have hL_pos := hinv.tree.hlen_pos
    have hq_le : q ≤ σ.history.length - 1 := by omega
    rcases Nat.lt_or_eq_of_le hq_le with hq_lt | hq_eq
    · by_cases hJq_lat : σ.J q ⊂ σ.latest
      · exact (Finset.mem_sdiff.mp hxJ).2 (le_of_lt hJq_lat hxq)
      · exact hinv.deadStart hph q hq_lt hJq_lat
          ⟨J, better_of_subset_better P hq_len hb hJq_sub⟩
    · have hx_lat : x ∈ σ.latest := by
        change x ∈ σ.J (σ.history.length - 1)
        rwa [← hq_eq]
      exact (Finset.mem_sdiff.mp hxJ).2 hx_lat
  · simp at hxp

/-- Downward induction showing every node `p ∈ [k, L)` is dead when no scan candidate lies `≥ k`. -/
private theorem dead_of_scan_no_candidate {n m : ℕ} (P : Problem n m) {σ : State n}
    (hinv : SoundInv P σ) {bound k : ℕ} (hph : σ.phase = .scan bound)
    (hno : ∀ p, Candidate P σ bound p → p < k) :
    ∀ p, k ≤ p → p < σ.history.length → Dead P σ p := by
  set L := σ.history.length
  have hmain : ∀ d : ℕ, ∀ p : ℕ, k ≤ p → p < L → L - 1 - p = d → Dead P σ p := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p hkp hpL hd
      by_cases hbp : bound ≤ p
      · exact (hinv.deadScan bound hph).1 p hbp hpL
      · have hpb : p < bound := not_le.mp hbp
        by_cases hss : σ.J p ⊂ σ.latest
        · have hnot_cand : ¬ Candidate P σ bound p :=
            fun hc => not_lt_of_ge hkp (hno p hc)
          have hrem_not_ne : ¬ (oldRemaining P σ p).Nonempty :=
            fun hne => hnot_cand ⟨hpb, hss, hne⟩
          rintro ⟨J, hb⟩
          have hnot_feas : ¬ P.lp.Feasible (σ.J p) := not_feasible_of_better P hpL hb
          simp only [BinaryLP.Feasible, not_forall, not_le] at hnot_feas
          obtain ⟨i, hslack⟩ := hnot_feas
          have hA_nonneg : ∀ j ∈ (J \ σ.J p) \ ∅, 0 ≤ P.lp.A i j := by
            intro j hj
            have hj_sdiff : j ∈ J \ σ.J p := (Finset.mem_sdiff.mp hj).1
            have hj_not_snap : j ∉ σ.snapshotC p := by
              intro hjsnap
              have hjcurr : j ∈ σ.currentC p := hinv.tree.hsnap_sub p hpL hjsnap
              obtain ⟨q, hpq, hqL, _, hJq_sub⟩ :=
                hinv.invC p hpL J hb j (Finset.mem_inter.mpr ⟨hj_sdiff, hjcurr⟩)
              have hdead_q : Dead P σ q :=
                ih (L - 1 - q) (by omega) q (by omega) hqL rfl
              exact hdead_q ⟨J, better_of_subset_better P hqL hb hJq_sub⟩
            have hj_not_oldD : j ∉ oldD P σ p := not_mem_oldD_of_better P hb hj_sdiff
            have hj_not_N : j ∉ σ.N p := by
              intro hjN
              apply hrem_not_ne
              refine ⟨j, Finset.mem_sdiff.mpr ⟨hjN, ?_⟩⟩
              rw [Finset.mem_union, not_or]
              exact ⟨hj_not_snap, hj_not_oldD⟩
            exact hinv.invInh p hpL J hb j hj_sdiff hj_not_N i hslack
          have hbound := feasible_slack_bound P (le_of_lt hb.2.1) hb.1 hA_nonneg
          simp [negativeSum] at hbound
          linarith
        · exact (hinv.deadScan bound hph).2 p hpb hss
  intro p hkp hpL
  exact hmain (L - 1 - p) p hkp hpL rfl

/-- At a selected scan candidate `k`, every better completion's elements outside `oldRemaining`
have nonnegative entries on violated rows of `σ.J k`. -/
private theorem selected_sdiff_oldRemaining_nonneg {n m : ℕ} (P : Problem n m) {σ : State n}
    (hinv : SoundInv P σ) {bound k : ℕ} (hph : σ.phase = .scan bound)
    (hselect : Selected P σ bound k) {J : Finset (Fin n)} (hb : Better P σ (σ.J k) J) :
    ∀ j ∈ (J \ σ.J k) \ oldRemaining P σ k,
      ∀ i : Fin m, P.lp.slack (σ.J k) i < 0 → 0 ≤ P.lp.A i j := by
  have hkL : k < σ.history.length := by
    have := (hinv.tree.hphase_scan bound hph).1
    have := hselect.1.1
    omega
  have hdead_above : ∀ q, k + 1 ≤ q → q < σ.history.length → Dead P σ q :=
    dead_of_scan_no_candidate P hinv hph
      (fun p hc => Nat.lt_succ_of_le (hselect.2 p hc))
  intro j hj i hslack
  have hj_sdiff : j ∈ J \ σ.J k := (Finset.mem_sdiff.mp hj).1
  have hj_not_rem : j ∉ oldRemaining P σ k := (Finset.mem_sdiff.mp hj).2
  have hj_not_snap : j ∉ σ.snapshotC k := by
    intro hjsnap
    have hjcurr : j ∈ σ.currentC k := hinv.tree.hsnap_sub k hkL hjsnap
    obtain ⟨q, hkq, hqL, _, hJq_sub⟩ :=
      hinv.invC k hkL J hb j (Finset.mem_inter.mpr ⟨hj_sdiff, hjcurr⟩)
    exact hdead_above q (by omega) hqL ⟨J, better_of_subset_better P hqL hb hJq_sub⟩
  have hj_not_oldD : j ∉ oldD P σ k := not_mem_oldD_of_better P hb hj_sdiff
  have hj_not_N : j ∉ σ.N k := by
    intro hjN
    apply hj_not_rem
    refine Finset.mem_sdiff.mpr ⟨hjN, ?_⟩
    rw [Finset.mem_union, not_or]
    exact ⟨hj_not_snap, hj_not_oldD⟩
  exact hinv.invInh k hkL J hb j hj_sdiff hj_not_N i hslack

/-- Unified forward-step lemma advancing `SoundInv` across `appendSolution P σ p X X`. -/
private theorem soundInv_appendSolution {n m : ℕ} (P : Problem n m) {σ : State n}
    (hinv : SoundInv P σ) (p : ℕ) (hp : p < σ.history.length) (X : Finset (Fin n))
    (hX_ne : X.Nonempty) (hX_sub : X ⊆ σ.N p) (hX_disj_curr : Disjoint X (σ.currentC p))
    (hp_anc : p = σ.history.length - 1 ∨ σ.J p ⊂ σ.latest)
    (hX_witness : ∀ J, Better P σ (σ.J p) J → ∀ x ∈ (J \ σ.J p) ∩ X, σ.J p ∪ X ⊆ J)
    (hdead_new : ∀ q < σ.history.length, ¬ (σ.J q ⊂ σ.J p ∪ X) → Dead P σ q) :
    SoundInv P (appendSolution P σ p X X) := by
  set τ := appendSolution P σ p X X
  set L := σ.history.length
  obtain ⟨htree_τ, hX_disj_Jp⟩ :=
    treeInv_appendSolution P σ hinv.tree p hp X hX_ne hX_sub hX_disj_curr hp_anc
  have hτ_len : τ.history.length = L + 1 := by simp [τ, appendSolution, L]
  have hτ_J_old : ∀ q < L, τ.J q = σ.J q := by
    intro q hq
    simp [τ, appendSolution, State.J, List.getElem?_append_left hq]
  have hτ_J_new : τ.J L = σ.J p ∪ X := by
    simp [τ, appendSolution, State.J, L]
  have hτ_latest : τ.latest = σ.J p ∪ X := by
    change τ.J (τ.history.length - 1) = σ.J p ∪ X
    have hlast : τ.history.length - 1 = L := by omega
    rw [hlast, hτ_J_new]
  have hcs_len : (cancelAt σ.cancelled p X).length = L := by
    rw [length_cancelAt, hinv.tree.hcanc_len]
  have hτ_curr_old : ∀ q < L, τ.currentC q = ((cancelAt σ.cancelled p X)[q]?).getD ∅ := by
    intro q hq
    have hq' : q < (cancelAt σ.cancelled p X).length := by omega
    simp [τ, appendSolution, State.currentC, List.getElem?_append_left hq']
  have hτ_curr_new : τ.currentC L = ∅ := by
    have hL' : L = (cancelAt σ.cancelled p X).length := hcs_len.symm
    simp [τ, appendSolution, State.currentC, hL']
  have hceil_le : ceiling P τ ≤ ceiling P σ := by
    have hmap : τ.history.map Record.J = σ.history.map Record.J ++ [σ.J p ∪ X] := by
      simp [τ, appendSolution]
    unfold ceiling
    rw [hmap]
    exact ceilingFrom_append_le P _ _
  have hdeadStart_τ : τ.phase = .start →
      ∀ q < τ.history.length - 1, ¬ (τ.J q ⊂ τ.latest) → Dead P τ q := by
    intro _ q hq hnot_ss
    have hqL : q < L := by omega
    rw [hτ_J_old q hqL, hτ_latest] at hnot_ss
    exact dead_of_ceil_le P hceil_le (hτ_J_old q hqL) (hdead_new q hqL hnot_ss)
  have hinvC_τ : ∀ w < τ.history.length, ∀ J, Better P τ (τ.J w) J →
      ∀ x ∈ (J \ τ.J w) ∩ τ.currentC w,
        ∃ q, w < q ∧ q < τ.history.length ∧ x ∈ τ.J q ∧ τ.J q ⊆ J := by
    intro w hw_len J hb_τ x hx
    have hw_le : w ≤ L := by omega
    rcases Nat.lt_or_eq_of_le hw_le with hwL | rfl
    · rw [hτ_J_old w hwL] at hb_τ hx
      rw [hτ_curr_old w hwL] at hx
      have hb_σ : Better P σ (σ.J w) J := better_of_ceil_le P hceil_le hb_τ
      by_cases hpw : p = w
      · subst hpw
        have hp_canc : p < σ.cancelled.length := hinv.tree.hcanc_len.symm ▸ hp
        rw [currentC_cancelAt_self σ.cancelled p X hp_canc] at hx
        obtain ⟨hx_sdiff, hx_cu⟩ := Finset.mem_inter.mp hx
        rcases Finset.mem_union.mp hx_cu with hx_old | hx_X
        · obtain ⟨q, hpq, hqL, hxq, hJq_sub⟩ :=
            hinv.invC p hp J hb_σ x (Finset.mem_inter.mpr ⟨hx_sdiff, hx_old⟩)
          exact ⟨q, hpq, by omega, by rwa [hτ_J_old q hqL], by rwa [hτ_J_old q hqL]⟩
        · refine ⟨L, hp, by omega, ?_, ?_⟩
          · rw [hτ_J_new]
            exact Finset.mem_union_right _ hx_X
          · rw [hτ_J_new]
            exact hX_witness J hb_σ x (Finset.mem_inter.mpr ⟨hx_sdiff, hx_X⟩)
      · rw [currentC_cancelAt_ne σ.cancelled p w X hpw] at hx
        obtain ⟨q, hwq, hqL, hxq, hJq_sub⟩ := hinv.invC w hwL J hb_σ x hx
        exact ⟨q, hwq, by omega, by rwa [hτ_J_old q hqL], by rwa [hτ_J_old q hqL]⟩
    · rw [hτ_curr_new] at hx
      simp at hx
  have hinvInh_τ : ∀ w < τ.history.length, ∀ J, Better P τ (τ.J w) J →
      ∀ j ∈ J \ τ.J w, j ∉ τ.N w →
        ∀ i : Fin m, P.lp.slack (τ.J w) i < 0 → 0 ≤ P.lp.A i j := by
    intro w hw_len J hb_τ j hj hj_notN i hslack
    have hw_le : w ≤ L := by omega
    rcases Nat.lt_or_eq_of_le hw_le with hwL | rfl
    · have hτ_N_w : τ.N w = σ.N w := by
        simp [τ, appendSolution, State.N, List.getElem?_append_left hwL]
      rw [hτ_J_old w hwL] at hb_τ hj hslack
      rw [hτ_N_w] at hj_notN
      exact hinv.invInh w hwL J (better_of_ceil_le P hceil_le hb_τ) j hj hj_notN i hslack
    · have hτ_N_L : τ.N L = newN P σ.history (cancelAt σ.cancelled p X) (τ.J L) := by
        have h1 : τ.N L = newN P σ.history (cancelAt σ.cancelled p X) (σ.J p ∪ X) := by
          simp [τ, appendSolution, State.N, L]
        rw [h1, ← hτ_J_new]
      rw [hτ_N_L] at hj_notN
      by_contra hnot_ge
      apply hj_notN
      simp only [newN, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, fun hall => hnot_ge (hall i hslack)⟩
      · intro hj_inh
        unfold inheritedC at hj_inh
        rw [Finset.mem_biUnion] at hj_inh
        obtain ⟨u, hu_range, hju⟩ := hj_inh
        have huL : u < L := Finset.mem_range.mp hu_range
        have hJu_eq : ((σ.history[u]?).map Record.J).getD ∅ = σ.J u := rfl
        rw [hJu_eq] at hju
        split_ifs at hju with hss_L
        · have hj_curr_u : j ∈ τ.currentC u := by
            rw [hτ_curr_old u huL]
            exact hju
          have hτJu_ss : τ.J u ⊂ τ.J L := by rwa [hτ_J_old u huL]
          have hb_u : Better P τ (τ.J u) J := ⟨hb_τ.1, hτJu_ss.trans hb_τ.2.1, hb_τ.2.2⟩
          have hj_not_Ju : j ∉ τ.J u := fun h =>
            (Finset.mem_sdiff.mp hj).2 (le_of_lt hτJu_ss h)
          have hj_inter : j ∈ (J \ τ.J u) ∩ τ.currentC u :=
            Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hj).1, hj_not_Ju⟩, hj_curr_u⟩
          obtain ⟨q, huq, hq_len, hjq, hJq_sub⟩ :=
            hinvC_τ u (by omega) J hb_u j hj_inter
          have hq_le : q ≤ L := by omega
          rcases Nat.lt_or_eq_of_le hq_le with hqL | rfl
          · by_cases hJq_lat : τ.J q ⊂ τ.latest
            · have hlat_eq : τ.latest = τ.J L := by rw [hτ_latest, hτ_J_new]
              rw [hlat_eq] at hJq_lat
              exact (Finset.mem_sdiff.mp hj).2 (le_of_lt hJq_lat hjq)
            · exact hdeadStart_τ rfl q (by omega) hJq_lat
                ⟨J, better_of_subset_better P hq_len hb_τ hJq_sub⟩
          · exact (Finset.mem_sdiff.mp hj).2 hjq
        · simp at hju
      · intro hceil_le_j
        have hmap : σ.history.map Record.J ++ [τ.J L] = τ.history.map Record.J := by
          rw [hτ_J_new]
          simp [τ, appendSolution]
        have hceil_eq : ceilingFrom P (σ.history.map Record.J ++ [τ.J L]) = ceiling P τ := by
          unfold ceiling
          rw [hmap]
        rw [hceil_eq] at hceil_le_j
        have hcost_le : (↑(P.lp.cost (τ.J L) + P.lp.c j) : WithTop ℝ) ≤ (↑(P.lp.cost J) : WithTop ℝ) :=
          WithTop.coe_le_coe.mpr (cost_add_mem_sdiff P (le_of_lt hb_τ.2.1) hj)
        exact not_lt_of_ge (hceil_le_j.trans hcost_le) hb_τ.2.2
  exact
    { tree := htree_τ
      invC := hinvC_τ
      invInh := hinvInh_τ
      deadStart := hdeadStart_τ
      deadScan := by intro bound h; simp [τ, appendSolution] at h
      deadStop := by intro h; simp [τ, appendSolution] at h }

/-! ### Step-by-Step Preservation of `SoundInv` -/

private theorem soundInv_step {n m : ℕ} (P : Problem n m) {σ τ : State n}
    (hinv : SoundInv P σ) (hs : Step P σ τ) : SoundInv P τ := by
  have hL_pos := hinv.tree.hlen_pos
  cases hs with
  | one_a hph hfeas =>
    obtain ⟨hc1, hc2, hc3⟩ := cancelOldD_spec P σ
    obtain ⟨hstart_eq, _⟩ := hinv.tree.hphase_start hph
    have htree_τ : TreeInv P (beginScan σ (cancelOldD P σ) (σ.history.length - 1)) := by
      refine treeInv_nonAppend P σ _ hinv.tree rfl hc1 (fun q => hc2 q) (by simp [beginScan]) ?_
      intro bound hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨le_rfl, ?_⟩
      intro q hq
      have hq_lt : q < σ.history.length := by omega
      have hsub := hc3 q hinv.tree.hcanc_len
      change ((cancelOldD P σ)[q]?).getD ∅ ⊆ σ.snapshotC q ∪ oldD P σ q
      exact hsub.trans (by rw [← hstart_eq q hq_lt]; rfl)
    refine
      { tree := htree_τ
        invC := ?_
        invInh := fun p hp J hb => hinv.invInh p hp J hb
        deadStart := by intro h; simp [beginScan] at h
        deadScan := ?_
        deadStop := by intro h; simp [beginScan] at h }
    · intro p hp J hb x hx
      obtain ⟨hx_sdiff, hx_curr⟩ := Finset.mem_inter.mp hx
      have hsub := hc3 p hinv.tree.hcanc_len hx_curr
      rcases Finset.mem_union.mp hsub with hx_old | hx_oldD
      · exact hinv.invC p hp J hb x (Finset.mem_inter.mpr ⟨hx_sdiff, hx_old⟩)
      · exact absurd hx_oldD (not_mem_oldD_of_better P hb hx_sdiff)
    · intro bound hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨?_, ?_⟩
      · intro q hq_ge hq_lt
        change q < σ.history.length at hq_lt
        have hq_eq : q = σ.history.length - 1 := by omega
        subst hq_eq
        rintro ⟨J, hb⟩
        exact not_feasible_of_better P hq_lt hb hfeas
      · intro q hq_lt hnot_ss
        exact hinv.deadStart hph q hq_lt hnot_ss
  | two_a hph hbad hempty =>
    obtain ⟨hstart_eq, _⟩ := hinv.tree.hphase_start hph
    have htree_τ : TreeInv P (beginScan σ σ.cancelled (σ.history.length - 1)) := by
      refine treeInv_nonAppend P σ _ hinv.tree rfl rfl (fun _ => Finset.Subset.refl _)
        (by simp [beginScan]) ?_
      intro bound hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨le_rfl, ?_⟩
      intro q hq
      have hq_lt : q < σ.history.length := by omega
      change σ.currentC q ⊆ σ.snapshotC q ∪ oldD P σ q
      rw [hstart_eq q hq_lt]
      exact Finset.subset_union_left
    have hdead_last : Dead P σ (σ.history.length - 1) := by
      rintro ⟨J, hb⟩
      simp only [BinaryLP.Feasible, not_forall, not_le] at hbad
      obtain ⟨i, hslack⟩ := hbad
      have hlat : σ.latest = σ.J (σ.history.length - 1) := rfl
      rw [hlat] at hslack
      have hA_nonneg : ∀ j ∈ (J \ σ.J (σ.history.length - 1)) \ ∅, 0 ≤ P.lp.A i j := by
        intro j hj
        have hj_sdiff : j ∈ J \ σ.J (σ.history.length - 1) := (Finset.mem_sdiff.mp hj).1
        have hj_notN : j ∉ σ.N (σ.history.length - 1) := by simp [hempty]
        exact hinv.invInh (σ.history.length - 1) (by omega) J hb j hj_sdiff hj_notN i hslack
      have hbound := feasible_slack_bound P (le_of_lt hb.2.1) hb.1 hA_nonneg
      simp [negativeSum] at hbound
      linarith
    refine
      { tree := htree_τ
        invC := hinv.invC
        invInh := hinv.invInh
        deadStart := by intro h; simp [beginScan] at h
        deadScan := ?_
        deadStop := by intro h; simp [beginScan] at h }
    intro bound hb
    simp only [beginScan, Phase.scan.injEq] at hb
    subst hb
    refine ⟨?_, fun q hq_lt hnot_ss => hinv.deadStart hph q hq_lt hnot_ss⟩
    intro q hq_ge hq_lt
    change q < σ.history.length at hq_lt
    have hq_eq : q = σ.history.length - 1 := by omega
    subst hq_eq
    exact hdead_last
  | three_a hph _ _ hfail =>
    obtain ⟨hstart_eq, _⟩ := hinv.tree.hphase_start hph
    have htree_τ : TreeInv P (beginScan σ σ.cancelled (σ.history.length - 1)) := by
      refine treeInv_nonAppend P σ _ hinv.tree rfl rfl (fun _ => Finset.Subset.refl _)
        (by simp [beginScan]) ?_
      intro bound hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨le_rfl, ?_⟩
      intro q hq
      have hq_lt : q < σ.history.length := by omega
      change σ.currentC q ⊆ σ.snapshotC q ∪ oldD P σ q
      rw [hstart_eq q hq_lt]
      exact Finset.subset_union_left
    have hdead_last : Dead P σ (σ.history.length - 1) := by
      rintro ⟨J, hb⟩
      apply hfail
      intro i hslack
      have hlat : σ.latest = σ.J (σ.history.length - 1) := rfl
      rw [hlat] at hslack ⊢
      exact feasible_slack_bound P (le_of_lt hb.2.1) hb.1 fun j hj =>
        hinv.invInh (σ.history.length - 1) (by omega) J hb j
          (Finset.mem_sdiff.mp hj).1 (Finset.mem_sdiff.mp hj).2 i hslack
    refine
      { tree := htree_τ
        invC := hinv.invC
        invInh := hinv.invInh
        deadStart := by intro h; simp [beginScan] at h
        deadScan := ?_
        deadStop := by intro h; simp [beginScan] at h }
    intro bound hb
    simp only [beginScan, Phase.scan.injEq] at hb
    subst hb
    refine ⟨?_, fun q hq_lt hnot_ss => hinv.deadStart hph q hq_lt hnot_ss⟩
    intro q hq_ge hq_lt
    change q < σ.history.length at hq_lt
    have hq_eq : q = σ.history.length - 1 := by omega
    subst hq_eq
    exact hdead_last
  | three_b j hph _ _ _ hchoice =>
    obtain ⟨_, hcurr_last⟩ := hinv.tree.hphase_start hph
    have hj_N : {j} ⊆ σ.N (σ.history.length - 1) := Finset.singleton_subset_iff.mpr hchoice.1
    have hdisj_curr : Disjoint ({j} : Finset (Fin n)) (σ.currentC (σ.history.length - 1)) := by
      rw [hcurr_last]
      exact Finset.disjoint_empty_right _
    obtain ⟨_, hdisj_Jp⟩ :=
      treeInv_appendSolution P σ hinv.tree (σ.history.length - 1) (by omega) {j}
        (Finset.singleton_nonempty j) hj_N hdisj_curr (Or.inl rfl)
    have hss_new : σ.J (σ.history.length - 1) ⊂ σ.J (σ.history.length - 1) ∪ {j} := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, fun heq => ?_⟩
      have hj_in : j ∈ σ.J (σ.history.length - 1) := by
        have : j ∈ σ.J (σ.history.length - 1) ∪ {j} :=
          Finset.mem_union_right _ (Finset.mem_singleton_self j)
        rwa [← heq] at this
      exact Finset.disjoint_singleton_left.mp hdisj_Jp hj_in
    refine soundInv_appendSolution P hinv (σ.history.length - 1) (by omega) {j}
      (Finset.singleton_nonempty j) hj_N hdisj_curr (Or.inl rfl) ?_ ?_
    · intro J hb x hx
      obtain ⟨hx_sdiff, hxj⟩ := Finset.mem_inter.mp hx
      rw [Finset.mem_singleton.mp hxj] at hx_sdiff
      exact Finset.union_subset (le_of_lt hb.2.1)
        (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hx_sdiff).1)
    · intro q hq_lt hnot_ss
      have hq_le : q ≤ σ.history.length - 1 := by omega
      rcases Nat.lt_or_eq_of_le hq_le with hq_lt' | rfl
      · apply hinv.deadStart hph q hq_lt'
        intro hss_lat
        exact hnot_ss (hss_lat.trans hss_new)
      · exact absurd hss_new hnot_ss
  | four_a hph _ _ hhold hnonstrict _ =>
    obtain ⟨_, hcurr_last⟩ := hinv.tree.hphase_start hph
    set F := equalityF P σ.latest (σ.N (σ.history.length - 1))
    have hF_ne : F.Nonempty := equalityF_nonempty P σ.latest _ hhold hnonstrict
    have hF_sub : F ⊆ σ.N (σ.history.length - 1) := equalityF_subset P σ.latest _
    have hdisj_curr : Disjoint F (σ.currentC (σ.history.length - 1)) := by
      rw [hcurr_last]
      exact Finset.disjoint_empty_right _
    obtain ⟨_, hdisj_Jp⟩ :=
      treeInv_appendSolution P σ hinv.tree (σ.history.length - 1) (by omega) F
        hF_ne hF_sub hdisj_curr (Or.inl rfl)
    have hss_new : σ.J (σ.history.length - 1) ⊂ σ.J (σ.history.length - 1) ∪ F := by
      obtain ⟨x₀, hx₀⟩ := hF_ne
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, fun heq => ?_⟩
      have hx_in : x₀ ∈ σ.J (σ.history.length - 1) := by
        have : x₀ ∈ σ.J (σ.history.length - 1) ∪ F := Finset.mem_union_right _ hx₀
        rwa [← heq] at this
      exact Finset.disjoint_left.mp hdisj_Jp hx₀ hx_in
    refine soundInv_appendSolution P hinv (σ.history.length - 1) (by omega) F
      hF_ne hF_sub hdisj_curr (Or.inl rfl) ?_ ?_
    · intro J hb _ _
      have hF_sdiff : F ⊆ J \ σ.J (σ.history.length - 1) :=
        equalityF_subset_sdiff P (le_of_lt hb.2.1) hb.1 fun j hj i hslack =>
          hinv.invInh (σ.history.length - 1) (by omega) J hb j
            (Finset.mem_sdiff.mp hj).1 (Finset.mem_sdiff.mp hj).2 i hslack
      exact Finset.union_subset (le_of_lt hb.2.1) (hF_sdiff.trans Finset.sdiff_subset)
    · intro q hq_lt hnot_ss
      have hq_le : q ≤ σ.history.length - 1 := by omega
      rcases Nat.lt_or_eq_of_le hq_le with hq_lt' | rfl
      · apply hinv.deadStart hph q hq_lt'
        intro hss_lat
        exact hnot_ss (hss_lat.trans hss_new)
      · exact absurd hss_new hnot_ss
  | four_b hph _ _ _ _ hcost =>
    obtain ⟨hstart_eq, _⟩ := hinv.tree.hphase_start hph
    have htree_τ : TreeInv P (beginScan σ
        (cancelAt σ.cancelled (σ.history.length - 1) (σ.N (σ.history.length - 1)))
        (σ.history.length - 1)) := by
      refine treeInv_nonAppend P σ _ hinv.tree rfl (length_cancelAt _ _ _)
        (fun q => subset_cancelAt _ _ q _) (by simp [beginScan]) ?_
      intro bound hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨le_rfl, ?_⟩
      intro q hq
      have hne : σ.history.length - 1 ≠ q := by omega
      have hq_lt : q < σ.history.length := by omega
      change ((cancelAt σ.cancelled (σ.history.length - 1) _)[q]?).getD ∅ ⊆ σ.snapshotC q ∪ oldD P σ q
      rw [currentC_cancelAt_ne _ _ q _ hne]
      change σ.currentC q ⊆ σ.snapshotC q ∪ oldD P σ q
      rw [hstart_eq q hq_lt]
      exact Finset.subset_union_left
    have hdead_last : Dead P σ (σ.history.length - 1) := by
      rintro ⟨J, hb⟩
      apply hcost
      set F := equalityF P σ.latest (σ.N (σ.history.length - 1))
      have hF_sdiff : F ⊆ J \ σ.latest :=
        equalityF_subset_sdiff P (le_of_lt hb.2.1) hb.1 fun j hj i hslack =>
          hinv.invInh (σ.history.length - 1) (by omega) J hb j
            (Finset.mem_sdiff.mp hj).1 (Finset.mem_sdiff.mp hj).2 i hslack
      unfold belowCeiling
      exact lt_of_le_of_lt
        (WithTop.coe_le_coe.mpr (cost_add_subset_sdiff P (le_of_lt hb.2.1) hF_sdiff)) hb.2.2
    refine
      { tree := htree_τ
        invC := ?_
        invInh := hinv.invInh
        deadStart := by intro h; simp [beginScan] at h
        deadScan := ?_
        deadStop := by intro h; simp [beginScan] at h }
    · intro p hp J hb x hx
      by_cases hp_eq : σ.history.length - 1 = p
      · subst hp_eq
        exact absurd ⟨J, hb⟩ hdead_last
      · change x ∈ (J \ σ.J p) ∩ ((cancelAt σ.cancelled (σ.history.length - 1) _)[p]?).getD ∅ at hx
        rw [currentC_cancelAt_ne _ _ p _ hp_eq] at hx
        exact hinv.invC p hp J hb x hx
    · intro bound hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨?_, fun q hq_lt hnot_ss => hinv.deadStart hph q hq_lt hnot_ss⟩
      intro q hq_ge hq_lt
      change q < σ.history.length at hq_lt
      have hq_eq : q = σ.history.length - 1 := by omega
      subst hq_eq
      exact hdead_last
  | five_a bound hph hnone =>
    have htree_τ : TreeInv P (stop σ) :=
      treeInv_nonAppend P σ _ hinv.tree rfl rfl (fun _ => Finset.Subset.refl _)
        (by simp [stop]) (by intro b hb; simp [stop] at hb)
    refine
      { tree := htree_τ
        invC := hinv.invC
        invInh := hinv.invInh
        deadStart := by intro h; simp [stop] at h
        deadScan := by intro b hb; simp [stop] at hb
        deadStop := ?_ }
    intro _ q hq
    exact dead_of_scan_no_candidate P hinv hph (fun p hc => absurd ⟨p, hc⟩ hnone) q (Nat.zero_le q) hq
  | six_a bound k hph hselect hfail =>
    obtain ⟨hb_le, hscan_sub⟩ := hinv.tree.hphase_scan bound hph
    have hk_bound : k < bound := hselect.1.1
    have htree_τ : TreeInv P (beginScan σ (cancelAt σ.cancelled k (oldRemaining P σ k)) k) := by
      refine treeInv_nonAppend P σ _ hinv.tree rfl (length_cancelAt _ _ _)
        (fun q => subset_cancelAt _ _ q _) (by simp [beginScan]) ?_
      intro b hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨by change k ≤ σ.history.length - 1; omega, ?_⟩
      intro q hq
      have hne : k ≠ q := by omega
      change ((cancelAt σ.cancelled k _)[q]?).getD ∅ ⊆ σ.snapshotC q ∪ oldD P σ q
      rw [currentC_cancelAt_ne _ k q _ hne]
      exact hscan_sub q (lt_trans hq hk_bound)
    have hdead_above : ∀ q, k + 1 ≤ q → q < σ.history.length → Dead P σ q :=
      dead_of_scan_no_candidate P hinv hph
        (fun p hc => Nat.lt_succ_of_le (hselect.2 p hc))
    have hdead_k : Dead P σ k := by
      rintro ⟨J, hb⟩
      apply hfail
      intro i hslack
      exact feasible_slack_bound P (le_of_lt hb.2.1) hb.1 fun j hj =>
        selected_sdiff_oldRemaining_nonneg P hinv hph hselect hb j hj i hslack
    refine
      { tree := htree_τ
        invC := ?_
        invInh := hinv.invInh
        deadStart := by intro h; simp [beginScan] at h
        deadScan := ?_
        deadStop := by intro h; simp [beginScan] at h }
    · intro p hp J hb x hx
      by_cases hkp : k = p
      · subst hkp
        exact absurd ⟨J, hb⟩ hdead_k
      · change x ∈ (J \ σ.J p) ∩ ((cancelAt σ.cancelled k _)[p]?).getD ∅ at hx
        rw [currentC_cancelAt_ne _ k p _ hkp] at hx
        exact hinv.invC p hp J hb x hx
    · intro b hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨?_, ?_⟩
      · intro q hkq hq_lt
        rcases Nat.eq_or_lt_of_le hkq with rfl | hlt
        · exact hdead_k
        · exact hdead_above q hlt hq_lt
      · intro q hqk hnot_ss
        exact (hinv.deadScan bound hph).2 q (lt_trans hqk hk_bound) hnot_ss
  | six_b bound k j hph hselect _ hchoice =>
    obtain ⟨hb_le, hscan_sub⟩ := hinv.tree.hphase_scan bound hph
    have hk_bound : k < bound := hselect.1.1
    have hk_len : k < σ.history.length := by omega
    have hj_rem : j ∈ oldRemaining P σ k := hchoice.1
    have hj_N : j ∈ σ.N k := (Finset.mem_sdiff.mp hj_rem).1
    have hj_not : j ∉ σ.snapshotC k ∪ oldD P σ k := (Finset.mem_sdiff.mp hj_rem).2
    have hdisj_curr : Disjoint ({j} : Finset (Fin n)) (σ.currentC k) := by
      rw [Finset.disjoint_singleton_left]
      intro hj_curr
      exact hj_not (hscan_sub k hk_bound hj_curr)
    obtain ⟨_, hdisj_Jk⟩ :=
      treeInv_appendSolution P σ hinv.tree k hk_len {j}
        (Finset.singleton_nonempty j) (Finset.singleton_subset_iff.mpr hj_N)
        hdisj_curr (Or.inr hselect.1.2.1)
    have hss_new : σ.J k ⊂ σ.J k ∪ {j} := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, fun heq => ?_⟩
      have hj_in : j ∈ σ.J k := by
        have : j ∈ σ.J k ∪ {j} := Finset.mem_union_right _ (Finset.mem_singleton_self j)
        rwa [← heq] at this
      exact Finset.disjoint_singleton_left.mp hdisj_Jk hj_in
    have hdead_above : ∀ q, k + 1 ≤ q → q < σ.history.length → Dead P σ q :=
      dead_of_scan_no_candidate P hinv hph
        (fun p hc => Nat.lt_succ_of_le (hselect.2 p hc))
    refine soundInv_appendSolution P hinv k hk_len {j}
      (Finset.singleton_nonempty j) (Finset.singleton_subset_iff.mpr hj_N)
      hdisj_curr (Or.inr hselect.1.2.1) ?_ ?_
    · intro J hb x hx
      obtain ⟨hx_sdiff, hxj⟩ := Finset.mem_inter.mp hx
      rw [Finset.mem_singleton.mp hxj] at hx_sdiff
      exact Finset.union_subset (le_of_lt hb.2.1)
        (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hx_sdiff).1)
    · intro q hq_lt hnot_ss
      rcases lt_trichotomy q k with hqk | rfl | hkq
      · apply (hinv.deadScan bound hph).2 q (lt_trans hqk hk_bound)
        intro hq_lat
        have hqk_ss : σ.J q ⊂ σ.J k :=
          ssubset_of_both_ssubset_latest P σ hinv.tree hqk hk_len hq_lat hselect.1.2.1
        exact hnot_ss (hqk_ss.trans hss_new)
      · exact absurd hss_new hnot_ss
      · exact hdead_above q hkq hq_lt
  | seven_a bound k hph hselect hhold hnonstrict _ =>
    obtain ⟨hb_le, hscan_sub⟩ := hinv.tree.hphase_scan bound hph
    have hk_bound : k < bound := hselect.1.1
    have hk_len : k < σ.history.length := by omega
    set F := equalityF P (σ.J k) (oldRemaining P σ k)
    have hF_ne : F.Nonempty := equalityF_nonempty P (σ.J k) _ hhold hnonstrict
    have hF_rem : F ⊆ oldRemaining P σ k := equalityF_subset P (σ.J k) _
    have hF_N : F ⊆ σ.N k := hF_rem.trans Finset.sdiff_subset
    have hdisj_curr : Disjoint F (σ.currentC k) := by
      rw [Finset.disjoint_left]
      intro x hxF hx_curr
      exact (Finset.mem_sdiff.mp (hF_rem hxF)).2 (hscan_sub k hk_bound hx_curr)
    obtain ⟨_, hdisj_Jk⟩ :=
      treeInv_appendSolution P σ hinv.tree k hk_len F
        hF_ne hF_N hdisj_curr (Or.inr hselect.1.2.1)
    have hss_new : σ.J k ⊂ σ.J k ∪ F := by
      obtain ⟨x₀, hx₀⟩ := hF_ne
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, fun heq => ?_⟩
      have hx_in : x₀ ∈ σ.J k := by
        have : x₀ ∈ σ.J k ∪ F := Finset.mem_union_right _ hx₀
        rwa [← heq] at this
      exact Finset.disjoint_left.mp hdisj_Jk hx₀ hx_in
    have hdead_above : ∀ q, k + 1 ≤ q → q < σ.history.length → Dead P σ q :=
      dead_of_scan_no_candidate P hinv hph
        (fun p hc => Nat.lt_succ_of_le (hselect.2 p hc))
    refine soundInv_appendSolution P hinv k hk_len F
      hF_ne hF_N hdisj_curr (Or.inr hselect.1.2.1) ?_ ?_
    · intro J hb _ _
      have hF_sdiff : F ⊆ J \ σ.J k :=
        equalityF_subset_sdiff P (le_of_lt hb.2.1) hb.1
          (selected_sdiff_oldRemaining_nonneg P hinv hph hselect hb)
      exact Finset.union_subset (le_of_lt hb.2.1) (hF_sdiff.trans Finset.sdiff_subset)
    · intro q hq_lt hnot_ss
      rcases lt_trichotomy q k with hqk | rfl | hkq
      · apply (hinv.deadScan bound hph).2 q (lt_trans hqk hk_bound)
        intro hq_lat
        have hqk_ss : σ.J q ⊂ σ.J k :=
          ssubset_of_both_ssubset_latest P σ hinv.tree hqk hk_len hq_lat hselect.1.2.1
        exact hnot_ss (hqk_ss.trans hss_new)
      · exact absurd hss_new hnot_ss
      · exact hdead_above q hkq hq_lt
  | seven_b bound k hph hselect _ _ hcost =>
    obtain ⟨hb_le, hscan_sub⟩ := hinv.tree.hphase_scan bound hph
    have hk_bound : k < bound := hselect.1.1
    have htree_τ : TreeInv P (beginScan σ (cancelAt σ.cancelled k (oldRemaining P σ k)) k) := by
      refine treeInv_nonAppend P σ _ hinv.tree rfl (length_cancelAt _ _ _)
        (fun q => subset_cancelAt _ _ q _) (by simp [beginScan]) ?_
      intro b hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨by change k ≤ σ.history.length - 1; omega, ?_⟩
      intro q hq
      have hne : k ≠ q := by omega
      change ((cancelAt σ.cancelled k _)[q]?).getD ∅ ⊆ σ.snapshotC q ∪ oldD P σ q
      rw [currentC_cancelAt_ne _ k q _ hne]
      exact hscan_sub q (lt_trans hq hk_bound)
    have hdead_above : ∀ q, k + 1 ≤ q → q < σ.history.length → Dead P σ q :=
      dead_of_scan_no_candidate P hinv hph
        (fun p hc => Nat.lt_succ_of_le (hselect.2 p hc))
    have hdead_k : Dead P σ k := by
      rintro ⟨J, hb⟩
      apply hcost
      set F := equalityF P (σ.J k) (oldRemaining P σ k)
      have hF_sdiff : F ⊆ J \ σ.J k :=
        equalityF_subset_sdiff P (le_of_lt hb.2.1) hb.1
          (selected_sdiff_oldRemaining_nonneg P hinv hph hselect hb)
      unfold belowCeiling
      exact lt_of_le_of_lt
        (WithTop.coe_le_coe.mpr (cost_add_subset_sdiff P (le_of_lt hb.2.1) hF_sdiff)) hb.2.2
    refine
      { tree := htree_τ
        invC := ?_
        invInh := hinv.invInh
        deadStart := by intro h; simp [beginScan] at h
        deadScan := ?_
        deadStop := by intro h; simp [beginScan] at h }
    · intro p hp J hb x hx
      by_cases hkp : k = p
      · subst hkp
        exact absurd ⟨J, hb⟩ hdead_k
      · change x ∈ (J \ σ.J p) ∩ ((cancelAt σ.cancelled k _)[p]?).getD ∅ at hx
        rw [currentC_cancelAt_ne _ k p _ hkp] at hx
        exact hinv.invC p hp J hb x hx
    · intro b hb
      simp only [beginScan, Phase.scan.injEq] at hb
      subst hb
      refine ⟨?_, ?_⟩
      · intro q hkq hq_lt
        rcases Nat.eq_or_lt_of_le hkq with rfl | hlt
        · exact hdead_k
        · exact hdead_above q hlt hq_lt
      · intro q hqk hnot_ss
        exact (hinv.deadScan bound hph).2 q (lt_trans hqk hk_bound) hnot_ss

private theorem soundInv_reachable {n m : ℕ} (P : Problem n m) {σ : State n}
    (hr : Reachable P σ) : SoundInv P σ := by
  induction hr with
  | refl => exact soundInv_init P
  | tail _ hs ih => exact soundInv_step P ih hs

end BalasAdditive.Convergence.SoundAux

open BalasAdditive.Convergence

theorem solution {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) (hphase : σ.phase = .start)
    (J : Finset (Fin n)) (hfeas : P.lp.Feasible J)
    (hstrict : σ.latest ⊂ J)
    (hcost : (↑(P.lp.cost J) : WithTop ℝ) < ceiling P σ) :
    Disjoint (J \ σ.latest) σ.C :=
  BalasAdditive.Convergence.SoundAux.lemma1_of_soundInv P
    (BalasAdditive.Convergence.SoundAux.soundInv_reachable P hr)
    hphase ⟨hfeas, hstrict, hcost⟩
