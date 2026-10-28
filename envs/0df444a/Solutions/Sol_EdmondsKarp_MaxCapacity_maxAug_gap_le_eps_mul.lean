-- Prove2me | solution 1 for EdmondsKarp.MaxCapacity.maxAug_gap_le_eps_mul
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:03:50.849935+00:00
-- url     : https://prove2.me/submissions/98232012-3991-483a-b256-37849f34ed08

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.MinMax
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation
import Definitions.Def_EdmondsKarp_MaxCapacity_Run
import Theorems.Thm_EdmondsKarp_MaxCapacity_cut_bound
import Theorems.Thm_EdmondsKarp_MaxCapacity_augment_isFlow

open EdmondsKarp.MaxCapacity

private lemma isFlow_of_isMaxAugRun {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (K : ℕ) (f : ℕ → V → V → ℝ)
    (P : ℕ → List V) (hrun : IsMaxAugRun N K f P) :
    ∀ j ≤ K, IsFlow N (f j) := by
  intro j hj
  induction j with
  | zero => exact hrun.1
  | succ j ih =>
    have hjK : j < K := Nat.lt_of_succ_le hj
    have hstep := hrun.2 j hjK
    rw [hstep.2]
    exact (augment_isFlow N (f j) (P j) (ih (Nat.le_of_lt hjK)) hstep.1.1).1

private lemma suffix_of_mem {V : Type} [DecidableEq V] {R : V → V → Prop} :
    ∀ {Q : List V} {u v : V},
      Q.Nodup → Q.getLast? = some v → (∀ e ∈ pathArcs Q, R e.1 e.2) → u ∈ Q →
      ∃ Q' : List V, Q'.Nodup ∧ Q'.head? = some u ∧ Q'.getLast? = some v ∧
        ∀ e ∈ pathArcs Q', R e.1 e.2
  | [], _, _, _, _, _, hu => nomatch hu
  | a :: l, u, v, hnodup, hlast, harcs, hu => by
    by_cases hua : u = a
    · subst u
      exact ⟨a :: l, hnodup, rfl, hlast, harcs⟩
    · have hul : u ∈ l := by
        rcases List.mem_cons.mp hu with rfl | h
        · exact absurd rfl hua
        · exact h
      cases l with
      | nil => cases hul
      | cons b l' =>
        have hnodup' : (b :: l').Nodup := (List.nodup_cons.mp hnodup).2
        have hlast' : (b :: l').getLast? = some v := hlast
        have harcs' : ∀ e ∈ pathArcs (b :: l'), R e.1 e.2 := by
          intro e he
          exact harcs e (List.mem_cons_of_mem (a, b) he)
        exact suffix_of_mem hnodup' hlast' harcs' hul

private lemma cons_reach {V : Type} [DecidableEq V] {R : V → V → Prop} {u w v : V} (huw : R u w)
    (hw : ∃ Q : List V, Q.Nodup ∧ Q.head? = some w ∧ Q.getLast? = some v ∧
      ∀ e ∈ pathArcs Q, R e.1 e.2) :
    ∃ Q' : List V, Q'.Nodup ∧ Q'.head? = some u ∧ Q'.getLast? = some v ∧
      ∀ e ∈ pathArcs Q', R e.1 e.2 := by
  rcases hw with ⟨Q, hnodup, hhead, hlast, harcs⟩
  by_cases huQ : u ∈ Q
  · exact suffix_of_mem hnodup hlast harcs huQ
  · cases Q with
    | nil => cases hhead
    | cons a l =>
      have haw : a = w := Option.some.inj hhead
      subst a
      refine ⟨u :: w :: l, List.nodup_cons.mpr ⟨huQ, hnodup⟩, rfl, hlast, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact huw
      · exact harcs e he'

private lemma lt_foldl_min {ε : ℝ} :
    ∀ (xs : List ℝ) (x : ℝ), ε < x → (∀ y ∈ xs, ε < y) → ε < xs.foldl min x
  | [], _, hx, _ => hx
  | y :: xs, x, hx, hxs =>
    lt_foldl_min xs (min x y)
      (lt_min hx (hxs y List.mem_cons_self))
      (fun z hz => hxs z (List.mem_cons_of_mem y hz))

private lemma lt_min?_getD_of_nonempty {ε : ℝ} :
    ∀ {L : List ℝ}, L ≠ [] → (∀ x ∈ L, ε < x) → ε < (L.min?).getD 0
  | [], hne, _ => absurd rfl hne
  | x :: xs, _, hall => by
    change ε < xs.foldl min x
    exact lt_foldl_min xs x (hall x List.mem_cons_self)
      (fun y hy => hall y (List.mem_cons_of_mem x hy))

private lemma pathArcs_ne_nil_of_head_ne_last {V : Type} {Q : List V} {u v : V}
    (huv : u ≠ v) (hhead : Q.head? = some u) (hlast : Q.getLast? = some v) :
    pathArcs Q ≠ [] := by
  cases Q with
  | nil => cases hhead
  | cons a l =>
    cases l with
    | nil =>
      have hau : a = u := Option.some.inj hhead
      have hav : a = v := Option.some.inj hlast
      exact absurd (hau.symm.trans hav) huv
    | cons b l' =>
      exact List.cons_ne_nil (a, b) (pathArcs (b :: l'))

/-- Proof of Theorem 2, p. 254: in a run of the labeling method with maximum augmentations, on a
network with integer capacities in which every `s`–`t` cut is crossed by at most `M > 1` arcs, if
`f*(t, s)` is the value of a maximum flow then `f*(t, s) − f^k(t, s) ≤ ε^k M` for every `k < K`,
where `ε^k = f^{k+1}(t, s) − f^k(t, s)`. -/
theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (M : ℕ) (_hM : 1 < M) (hcross : CrossArcsBounded N M)
    (g : V → V → ℝ) (hg : IsMaxFlow N g)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsMaxAugRun N K f P)
    (k : ℕ) (hk : k < K) :
    g N.t N.s - f k N.t N.s ≤ (f (k + 1) N.t N.s - f k N.t N.s) * (M : ℝ) := by
  have hfk : IsFlow N (f k) := isFlow_of_isMaxAugRun N K f P hrun k (Nat.le_of_lt hk)
  have hstep := hrun.2 k hk
  have hPk_max : IsMaxAugPath N (f k) (P k) := hstep.1
  have hfk1 : f (k + 1) = augment N (f k) (P k) := hstep.2
  have haug := augment_isFlow N (f k) (P k) hfk hPk_max.1
  set ε : ℝ := pathEps N (f k) (P k)
  have heps_pos : 0 < ε := haug.2.1
  have heps_eq : f (k + 1) N.t N.s - f k N.t N.s = ε := by
    rw [hfk1]
    linarith [haug.2.2]
  let R : V → V → Prop := fun u v => ResArc N (f k) u v ∧ ε < stepEps N (f k) u v
  let Reach : V → Prop := fun u =>
    ∃ Q : List V, Q.Nodup ∧ Q.head? = some u ∧ Q.getLast? = some N.t ∧
      ∀ e ∈ pathArcs Q, R e.1 e.2
  classical
  let X : Finset V := Finset.univ.filter (fun u => ¬ Reach u)
  have hsX : N.s ∈ X := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ N.s, ?_⟩
    rintro ⟨Q, hnodup, hhead, hlast, harcs⟩
    have hQ_aug : IsAugPath N (f k) Q :=
      ⟨hnodup, hhead, hlast, fun e he => (harcs e he).1⟩
    have hQ_le : pathEps N (f k) Q ≤ ε := hPk_max.2 Q hQ_aug
    have hne : pathArcs Q ≠ [] :=
      pathArcs_ne_nil_of_head_ne_last N.source_ne_sink hhead hlast
    have hmap_ne : (pathArcs Q).map (fun e => stepEps N (f k) e.1 e.2) ≠ [] := by
      intro h
      exact hne (List.map_eq_nil_iff.mp h)
    have hQ_gt : ε < pathEps N (f k) Q := by
      apply lt_min?_getD_of_nonempty hmap_ne
      intro x hx
      rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
      exact (harcs e he).2
    linarith
  have htX : N.t ∉ X := by
    intro ht
    have hnot : ¬ Reach N.t := (Finset.mem_filter.mp ht).2
    refine hnot ⟨[N.t], List.nodup_singleton N.t, rfl, rfl, ?_⟩
    intro e he
    cases he
  have hno_R : ∀ u v, u ∈ X → v ∉ X → ¬ R u v := by
    intro u v huX hvX hRuv
    have hu_not : ¬ Reach u := (Finset.mem_filter.mp huX).2
    have hv_reach : Reach v := by
      by_contra hnv
      exact hvX (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hnv⟩)
    exact hu_not (cons_reach hRuv hv_reach)
  let F_out : Finset (V × V) := N.A.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X)
  let F_in : Finset (V × V) := N.A.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)
  have hout_bound : ∀ p ∈ F_out, N.c p.1 p.2 - f k p.1 p.2 ≤ ε := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpA, hp1, hp2⟩
    have hnotR : ¬ R p.1 p.2 := hno_R p.1 p.2 hp1 hp2
    by_cases hrev : (p.2, p.1) ∈ N.A
    · have hstep_eq : stepEps N (f k) p.1 p.2 = N.c p.1 p.2 - f k p.1 p.2 + f k p.2 p.1 := by
        simp [stepEps, hpA, hrev]
      have hf_nonneg : 0 ≤ f k p.2 p.1 :=
        hfk.1 p.2 p.1 (Finset.mem_insert_of_mem hrev)
      have hcap_le : f k p.1 p.2 ≤ N.c p.1 p.2 :=
        hfk.2.1 p.1 p.2 hpA
      have hstep_le : stepEps N (f k) p.1 p.2 ≤ ε := by
        by_contra hgt
        have hgt' : ε < stepEps N (f k) p.1 p.2 := not_le.mp hgt
        have hres : ResArc N (f k) p.1 p.2 := by
          by_cases hpos : 0 < N.c p.1 p.2 - f k p.1 p.2
          · exact Or.inl ⟨hpA, hpos⟩
          · exact Or.inr ⟨hrev, by linarith⟩
        exact hnotR ⟨hres, hgt'⟩
      linarith
    · have hstep_eq : stepEps N (f k) p.1 p.2 = N.c p.1 p.2 - f k p.1 p.2 := by
        simp [stepEps, hpA, hrev]
      by_contra hgt
      have hgt' : ε < N.c p.1 p.2 - f k p.1 p.2 := not_le.mp hgt
      have hres : ResArc N (f k) p.1 p.2 := Or.inl ⟨hpA, by linarith⟩
      exact hnotR ⟨hres, by linarith⟩
  have hin_bound : ∀ q ∈ F_in, f k q.1 q.2 ≤ ε := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqA, hq1, hq2⟩
    have hnotR : ¬ R q.2 q.1 := hno_R q.2 q.1 hq2 hq1
    by_cases hfwd : (q.2, q.1) ∈ N.A
    · have hstep_eq : stepEps N (f k) q.2 q.1 = N.c q.2 q.1 - f k q.2 q.1 + f k q.1 q.2 := by
        simp [stepEps, hfwd, hqA]
      have hf_nonneg : 0 ≤ f k q.1 q.2 :=
        hfk.1 q.1 q.2 (Finset.mem_insert_of_mem hqA)
      have hcap_le : f k q.2 q.1 ≤ N.c q.2 q.1 :=
        hfk.2.1 q.2 q.1 hfwd
      have hstep_le : stepEps N (f k) q.2 q.1 ≤ ε := by
        by_contra hgt
        have hgt' : ε < stepEps N (f k) q.2 q.1 := not_le.mp hgt
        have hres : ResArc N (f k) q.2 q.1 := by
          by_cases hpos : 0 < N.c q.2 q.1 - f k q.2 q.1
          · exact Or.inl ⟨hfwd, hpos⟩
          · exact Or.inr ⟨hqA, by linarith⟩
        exact hnotR ⟨hres, hgt'⟩
      linarith
    · have hstep_eq : stepEps N (f k) q.2 q.1 = f k q.1 q.2 := by
        simp [stepEps, hfwd]
      by_contra hgt
      have hgt' : ε < f k q.1 q.2 := not_le.mp hgt
      have hres : ResArc N (f k) q.2 q.1 := Or.inr ⟨hqA, by linarith⟩
      exact hnotR ⟨hres, by linarith⟩
  have hsum_out : ∑ p ∈ F_out, (N.c p.1 p.2 - f k p.1 p.2) ≤ (F_out.card : ℝ) * ε := by
    calc ∑ p ∈ F_out, (N.c p.1 p.2 - f k p.1 p.2)
      _ ≤ ∑ _p ∈ F_out, ε := Finset.sum_le_sum hout_bound
      _ = (F_out.card : ℝ) * ε := by simp [Finset.sum_const, nsmul_eq_mul]
  have hsum_in : ∑ q ∈ F_in, f k q.1 q.2 ≤ (F_in.card : ℝ) * ε := by
    calc ∑ q ∈ F_in, f k q.1 q.2
      _ ≤ ∑ _q ∈ F_in, ε := Finset.sum_le_sum hin_bound
      _ = (F_in.card : ℝ) * ε := by simp [Finset.sum_const, nsmul_eq_mul]
  have hdisj : Disjoint F_out F_in := by
    rw [Finset.disjoint_left]
    intro p hp_out hp_in
    exact (Finset.mem_filter.mp hp_in).2.1 (Finset.mem_filter.mp hp_out).2.1
  have hsub : F_out ∪ F_in ⊆
      N.arcs.filter (fun p => (p.1 ∈ X ∧ p.2 ∉ X) ∨ (p.1 ∉ X ∧ p.2 ∈ X)) := by
    intro p hp
    rw [Finset.mem_filter]
    rcases Finset.mem_union.mp hp with hp_out | hp_in
    · rcases Finset.mem_filter.mp hp_out with ⟨hpA, hpX⟩
      exact ⟨Finset.mem_insert_of_mem hpA, Or.inl hpX⟩
    · rcases Finset.mem_filter.mp hp_in with ⟨hpA, hpX⟩
      exact ⟨Finset.mem_insert_of_mem hpA, Or.inr hpX⟩
  have hcard_le_cross : F_out.card + F_in.card ≤ crossArcCount N X := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  have hcross_le_M : crossArcCount N X ≤ M := hcross X hsX htX
  have hcard_le_M : (F_out.card : ℝ) + (F_in.card : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast le_trans hcard_le_cross hcross_le_M
  have hcut_g := cut_bound N hcap X hsX htX g hg.1
  have hcut_fk := cut_bound N hcap X hsX htX (f k) hfk
  have hg_le_cap : g N.t N.s ≤ cutCap N X := by linarith [hcut_g.1, hcut_g.2]
  have hcap_sub_fk :
      cutCap N X - cutFlowOut N (f k) X = ∑ p ∈ F_out, (N.c p.1 p.2 - f k p.1 p.2) := by
    change (∑ p ∈ F_out, N.c p.1 p.2) - (∑ p ∈ F_out, f k p.1 p.2) =
      ∑ p ∈ F_out, (N.c p.1 p.2 - f k p.1 p.2)
    rw [← Finset.sum_sub_distrib]
  have hflow_in_eq : cutFlowIn N (f k) X = ∑ q ∈ F_in, f k q.1 q.2 := rfl
  have hmul_le : (F_out.card : ℝ) * ε + (F_in.card : ℝ) * ε ≤
      (f (k + 1) N.t N.s - f k N.t N.s) * (M : ℝ) := by
    calc (F_out.card : ℝ) * ε + (F_in.card : ℝ) * ε
      _ = ((F_out.card : ℝ) + (F_in.card : ℝ)) * ε := by rw [add_mul]
      _ ≤ (M : ℝ) * ε := mul_le_mul_of_nonneg_right hcard_le_M (le_of_lt heps_pos)
      _ = ε * (M : ℝ) := mul_comm (M : ℝ) ε
      _ = (f (k + 1) N.t N.s - f k N.t N.s) * (M : ℝ) := by rw [heps_eq]
  linarith [hcut_fk.1, hg_le_cap, hcap_sub_fk, hflow_in_eq, hsum_out, hsum_in, hmul_le]
