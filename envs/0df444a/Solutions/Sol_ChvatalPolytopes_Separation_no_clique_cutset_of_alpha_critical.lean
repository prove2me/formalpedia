-- Prove2me | solution 1 for ChvatalPolytopes.Separation.no_clique_cutset_of_alpha_critical
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:23:07.882647+00:00
-- url     : https://prove2.me/submissions/a35a9c5b-db53-4b97-9edd-694b7ad5a598

import Mathlib
import Definitions.Def_ChvatalPolytopes_Separation_AlphaCritical
import Definitions.Def_ChvatalPolytopes_Separation_IsCutset



namespace ChvatalPolytopes.Separation

open Classical

lemma ncc_critT {V : Type*} [Fintype V] (G : SimpleGraph V) (hcrit : IsAlphaCritical G)
    {p q : V} (h : G.Adj p q) :
    ∃ T : Finset V, T.card = G.indepNum + 1 ∧ p ∈ T ∧ q ∈ T ∧
      ∀ a ∈ T, ∀ b ∈ T, G.Adj a b → (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  obtain ⟨_, h2⟩ := hcrit s(p, q) h
  obtain ⟨T, hT⟩ := (G.deleteEdges {s(p, q)}).exists_isNIndepSet_indepNum
  have hprop : ∀ a ∈ T, ∀ b ∈ T, G.Adj a b → (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
    intro a ha b hb hab
    by_contra hne
    have hab' : (G.deleteEdges {s(p, q)}).Adj a b := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hab, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      tauto
    exact hT.isIndepSet (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hab.ne hab'
  have hcard : T.card = G.indepNum + 1 := by rw [hT.card_eq, h2]
  by_cases hpq : p ∈ T ∧ q ∈ T
  · exact ⟨T, hcard, hpq.1, hpq.2, hprop⟩
  · exfalso
    have hind : G.IsIndepSet (T : Set V) := by
      intro a ha b hb _ hab
      rcases hprop a ha b hb hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpq ⟨ha, hb⟩
      · exact hpq ⟨hb, ha⟩
    have := hind.card_le_indepNum
    omega

lemma ncc_indep_sub {V : Type*} (G : SimpleGraph V) {T S : Finset V} {p q : V}
    (hT : ∀ a ∈ T, ∀ b ∈ T, G.Adj a b → (a = p ∧ b = q) ∨ (a = q ∧ b = p))
    (hS : S ⊆ T) (hnot : p ∉ S ∨ q ∉ S) : G.IsIndepSet (S : Set V) := by
  intro a ha b hb hne hab
  have ha' : a ∈ S := ha
  have hb' : b ∈ S := hb
  rcases hT a (hS ha') b (hS hb') hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

lemma ncc_glue {V : Type*} [DecidableEq V] (G : SimpleGraph V) {S1 S2 : Finset V}
    (h1 : G.IsIndepSet (S1 : Set V)) (h2 : G.IsIndepSet (S2 : Set V))
    (hc : ∀ a ∈ S1, ∀ b ∈ S2, ¬ G.Adj a b) : G.IsIndepSet ((S1 ∪ S2 : Finset V) : Set V) := by
  intro a ha b hb hne hab
  have ha' : a ∈ S1 ∪ S2 := ha
  have hb' : b ∈ S1 ∪ S2 := hb
  rw [Finset.mem_union] at ha' hb'
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · exact h1 ha' hb' hne hab
  · exact hc a ha' b hb' hab
  · exact hc b hb' a ha' hab.symm
  · exact h2 ha' hb' hne hab

lemma ncc_split {V : Type*} [DecidableEq V] (T : Finset V) (C K D : Set V)
    [DecidablePred (· ∈ C)] [DecidablePred (· ∈ K)] [DecidablePred (· ∈ D)] (hcov : ∀ v, v ∈ C ∨ v ∈ K ∨ v ∈ D) :
    T.card ≤ (T.filter (· ∈ C)).card + (T.filter (· ∈ K)).card + (T.filter (· ∈ D)).card := by
  have h1 : T ⊆ T.filter (· ∈ C) ∪ T.filter (· ∈ K) ∪ T.filter (· ∈ D) := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases hcov v with h | h | h <;> tauto
  calc T.card ≤ _ := Finset.card_le_card h1
    _ ≤ _ := (Finset.card_union_le _ _).trans (by
          have := Finset.card_union_le (T.filter (· ∈ C)) (T.filter (· ∈ K)); omega)

lemma ncc_card3 {V : Type*} [DecidableEq V] (A B : Finset V) (k : V) (C K D : Set V)
    (hA : ∀ a ∈ A, a ∈ C) (hB : ∀ b ∈ B, b ∈ D) (hk : k ∈ K)
    (hCK : ∀ v, v ∈ C → v ∉ K) (hCD : ∀ v, v ∈ C → v ∉ D) (hKD : ∀ v, v ∈ K → v ∉ D) :
    (A ∪ {k} ∪ B).card = A.card + 1 + B.card := by
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_singleton]
  · rw [Finset.disjoint_singleton_right]; exact fun h => hCK k (hA k h) hk
  · rw [Finset.disjoint_left]
    intro v hv hvB
    rw [Finset.mem_union, Finset.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hCD v (hA v hv) (hB v hvB)
    · exact hKD _ hk (hB _ hvB)

theorem ncc_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hcrit : IsAlphaCritical G)
    (K : Set V) (hK : G.IsClique K) :
    ¬ IsCutset G K := by
  rintro ⟨x, y, hx, hy, hxy⟩
  let C : Set V := {v | ∃ hv : v ∉ K, (G.induce Kᶜ).Reachable ⟨x, hx⟩ ⟨v, hv⟩}
  let D : Set V := {v | v ∉ K ∧ v ∉ C}
  have xC : x ∈ C := ⟨hx, SimpleGraph.Reachable.refl _⟩
  have yD : y ∈ D := ⟨hy, fun ⟨hy', h⟩ => hxy h⟩
  have noCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d := by
    rintro c ⟨hc, hrc⟩ d ⟨hdK, hdC⟩ hadj
    exact hdC ⟨hdK, hrc.trans
      (SimpleGraph.Adj.reachable (G := G.induce Kᶜ) (u := ⟨c, hc⟩) (v := ⟨d, hdK⟩) hadj)⟩
  have hCK : ∀ v, v ∈ C → v ∉ K := fun v h => h.1
  have hCD : ∀ v, v ∈ C → v ∉ D := fun v h h' => h'.2 h
  have hKD : ∀ v, v ∈ K → v ∉ D := fun v h h' => h'.1 h
  have hcov : ∀ v, v ∈ C ∨ v ∈ K ∨ v ∈ D := by
    intro v
    by_cases h1 : v ∈ C
    · exact Or.inl h1
    · by_cases h2 : v ∈ K
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h2, h1⟩)
  obtain ⟨p⟩ := hconn.preconnected x y
  obtain ⟨d1, -, hd1C, hd1n⟩ := p.exists_boundary_dart C xC (fun h => yD.2 h)
  have hk : d1.snd ∈ K := by
    by_contra h
    exact noCD _ hd1C _ ⟨h, hd1n⟩ d1.adj
  obtain ⟨q⟩ := hconn.preconnected y x
  obtain ⟨d2, -, hd2D, hd2n⟩ := q.exists_boundary_dart D yD (fun h => h.2 xC)
  have hk' : d2.snd ∈ K := by
    by_contra h
    have : d2.snd ∈ C := by
      by_contra h'
      exact hd2n ⟨h, h'⟩
    exact noCD _ this _ hd2D d2.adj.symm
  set u := d1.fst with hu
  set k := d1.snd with hkdef
  set w := d2.fst with hw
  set k' := d2.snd with hk'def
  have huk : G.Adj u k := d1.adj
  have hwk : G.Adj w k' := d2.adj
  clear_value u k w k'
  obtain ⟨T1, hT1c, huT1, hkT1, hT1⟩ := ncc_critT G hcrit huk
  obtain ⟨T2, hT2c, hwT2, hkT2, hT2⟩ := ncc_critT G hcrit hwk
  -- T1 ∩ K ⊆ {k}
  have hK1 : (T1.filter (· ∈ K)).card ≤ 1 := by
    have : T1.filter (· ∈ K) ⊆ {k} := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_singleton]
      by_contra hne
      rcases hT1 a ha.1 k hkT1 (hK ha.2 hk hne) with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hCK _ hd1C ha.2
      · exact hne rfl
    simpa using Finset.card_le_card this
  have hK2 : (T2.filter (· ∈ K)).card ≤ 1 := by
    have : T2.filter (· ∈ K) ⊆ {k'} := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_singleton]
      by_contra hne
      rcases hT2 a ha.1 k' hkT2 (hK ha.2 hk' hne) with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hd2D.1 ha.2
      · exact hne rfl
    simpa using Finset.card_le_card this
  have s1 := ncc_split T1 C K D hcov
  have s2 := ncc_split T2 C K D hcov
  -- Z = T1 ∩ C ∪ T2 ∩ D
  have hZ : G.IsIndepSet ((T1.filter (· ∈ C) ∪ T2.filter (· ∈ D) : Finset V) : Set V) := by
    apply ncc_glue
    · exact ncc_indep_sub G hT1 (Finset.filter_subset _ _)
        (Or.inr (fun h => hCK _ (Finset.mem_filter.1 h).2 hk))
    · exact ncc_indep_sub G hT2 (Finset.filter_subset _ _)
        (Or.inr (fun h => hKD _ hk' (Finset.mem_filter.1 h).2))
    · intro a ha b hb
      exact noCD a (Finset.mem_filter.1 ha).2 b (Finset.mem_filter.1 hb).2
  have hZc : (T1.filter (· ∈ C) ∪ T2.filter (· ∈ D)).card =
      (T1.filter (· ∈ C)).card + (T2.filter (· ∈ D)).card := by
    rw [Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact hCD v (Finset.mem_filter.1 hv).2 (Finset.mem_filter.1 hv').2
  have hZle := hZ.card_le_indepNum
  rw [hZc] at hZle
  by_cases hkk : k = k'
  · subst hkk
    -- X = T2 ∩ C ∪ {k} ∪ T1 ∩ D
    have hX : G.IsIndepSet ((T2.filter (· ∈ C) ∪ {k} ∪ T1.filter (· ∈ D) : Finset V) : Set V) := by
      apply ncc_glue
      · apply ncc_indep_sub G hT2 (p := w) (q := k)
        · intro v hv
          rw [Finset.mem_union, Finset.mem_singleton] at hv
          rcases hv with hv | rfl
          · exact (Finset.mem_filter.1 hv).1
          · exact hkT2
        · left
          intro h
          rw [Finset.mem_union, Finset.mem_singleton] at h
          rcases h with h | h
          · exact hCD _ (Finset.mem_filter.1 h).2 hd2D
          · exact hd2D.1 (h ▸ hk)
      · exact ncc_indep_sub G hT1 (Finset.filter_subset _ _)
          (Or.inl (fun h => hCD _ hd1C (Finset.mem_filter.1 h).2))
      · intro a ha b hb hab
        rw [Finset.mem_union, Finset.mem_singleton] at ha
        have hb' := Finset.mem_filter.1 hb
        rcases ha with ha | rfl
        · exact noCD a (Finset.mem_filter.1 ha).2 b hb'.2 hab
        · rcases hT1 a hkT1 b hb'.1 hab with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact hKD _ hk hb'.2
          · exact hCD _ hd1C hb'.2
    have hXc : (T2.filter (· ∈ C) ∪ {k} ∪ T1.filter (· ∈ D)).card =
        (T2.filter (· ∈ C)).card + 1 + (T1.filter (· ∈ D)).card :=
      ncc_card3 _ _ k C K D (fun a ha => (Finset.mem_filter.1 ha).2)
        (fun a ha => (Finset.mem_filter.1 ha).2) hk hCK hCD hKD
    have hXle := hX.card_le_indepNum
    rw [hXc] at hXle

    omega
  · obtain ⟨T3, hT3c, hkT3, hk'T3, hT3⟩ := ncc_critT G hcrit (hK hk hk' hkk)
    have hK3 : (T3.filter (· ∈ K)).card ≤ 2 := by
      have : T3.filter (· ∈ K) ⊆ {k, k'} := by
        intro a ha
        rw [Finset.mem_filter] at ha
        rw [Finset.mem_insert, Finset.mem_singleton]
        by_contra hne
        push_neg at hne
        rcases hT3 a ha.1 k hkT3 (hK ha.2 hk hne.1) with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact hne.1 rfl
        · exact hne.2 rfl
      exact (Finset.card_le_card this).trans Finset.card_le_two
    have s3 := ncc_split T3 C K D hcov
    -- X = T2 ∩ C ∪ {k'} ∪ T3 ∩ D
    have hX : G.IsIndepSet ((T2.filter (· ∈ C) ∪ {k'} ∪ T3.filter (· ∈ D) : Finset V) : Set V) := by
      apply ncc_glue
      · apply ncc_indep_sub G hT2 (p := w) (q := k')
        · intro v hv
          rw [Finset.mem_union, Finset.mem_singleton] at hv
          rcases hv with hv | rfl
          · exact (Finset.mem_filter.1 hv).1
          · exact hkT2
        · left
          intro h
          rw [Finset.mem_union, Finset.mem_singleton] at h
          rcases h with h | h
          · exact hCD _ (Finset.mem_filter.1 h).2 hd2D
          · exact hd2D.1 (h ▸ hk')
      · exact ncc_indep_sub G hT3 (Finset.filter_subset _ _)
          (Or.inl (fun h => hKD _ hk (Finset.mem_filter.1 h).2))
      · intro a ha b hb hab
        rw [Finset.mem_union, Finset.mem_singleton] at ha
        have hb' := Finset.mem_filter.1 hb
        rcases ha with ha | rfl
        · exact noCD a (Finset.mem_filter.1 ha).2 b hb'.2 hab
        · rcases hT3 a hk'T3 b hb'.1 hab with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact hKD _ hk' hb'.2
          · exact hKD _ hk hb'.2
    -- Y = T3 ∩ C ∪ {k} ∪ T1 ∩ D
    have hY : G.IsIndepSet ((T3.filter (· ∈ C) ∪ {k} ∪ T1.filter (· ∈ D) : Finset V) : Set V) := by
      apply ncc_glue
      · apply ncc_indep_sub G hT3 (p := k) (q := k')
        · intro v hv
          rw [Finset.mem_union, Finset.mem_singleton] at hv
          rcases hv with hv | rfl
          · exact (Finset.mem_filter.1 hv).1
          · exact hkT3
        · right
          intro h
          rw [Finset.mem_union, Finset.mem_singleton] at h
          rcases h with h | h
          · exact hCK _ (Finset.mem_filter.1 h).2 hk'
          · exact hkk h.symm
      · exact ncc_indep_sub G hT1 (Finset.filter_subset _ _)
          (Or.inl (fun h => hCD _ hd1C (Finset.mem_filter.1 h).2))
      · intro a ha b hb hab
        rw [Finset.mem_union, Finset.mem_singleton] at ha
        have hb' := Finset.mem_filter.1 hb
        rcases ha with ha | rfl
        · exact noCD a (Finset.mem_filter.1 ha).2 b hb'.2 hab
        · rcases hT1 a hkT1 b hb'.1 hab with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact hKD _ hk hb'.2
          · exact hCD _ hd1C hb'.2
    have hXc : (T2.filter (· ∈ C) ∪ {k'} ∪ T3.filter (· ∈ D)).card =
        (T2.filter (· ∈ C)).card + 1 + (T3.filter (· ∈ D)).card :=
      ncc_card3 _ _ k' C K D (fun a ha => (Finset.mem_filter.1 ha).2)
        (fun a ha => (Finset.mem_filter.1 ha).2) hk' hCK hCD hKD
    have hYc : (T3.filter (· ∈ C) ∪ {k} ∪ T1.filter (· ∈ D)).card =
        (T3.filter (· ∈ C)).card + 1 + (T1.filter (· ∈ D)).card :=
      ncc_card3 _ _ k C K D (fun a ha => (Finset.mem_filter.1 ha).2)
        (fun a ha => (Finset.mem_filter.1 ha).2) hk hCK hCD hKD
    have hXle := hX.card_le_indepNum
    have hYle := hY.card_le_indepNum
    rw [hXc] at hXle
    rw [hYc] at hYle
    omega

end ChvatalPolytopes.Separation

open ChvatalPolytopes.Separation


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (hcrit : IsAlphaCritical G)
    (K : Set V) (hK : G.IsClique K) :
    ¬ IsCutset G K := by
  exact ncc_core G hconn hcrit K hK
