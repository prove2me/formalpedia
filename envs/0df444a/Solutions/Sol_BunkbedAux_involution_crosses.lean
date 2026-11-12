-- Prove2me | solution 1 for BunkbedAux.involution_crosses
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T01:50:10.419825+00:00
-- url     : https://prove2.me/submissions/2cfc463b-5903-4a74-a6f3-7f4cede40d07

import Definitions.Def_BunkbedWZSurgery
open Bunkbed Bunkbed.Hyper Finset SimpleGraph


/-- which pairs of a triple a state joins -/
def joinsAB (σ : WZ) : Prop := σ = .abc ∨ σ = .ab_c
def joinsBC (σ : WZ) : Prop := σ = .abc ∨ σ = .a_bc
def joinsAC (σ : WZ) : Prop := σ = .abc ∨ σ = .ac_b

/-- The edges a state contributes, as a three-way alternative. -/
lemma mem_edges_iff {V : Type*} [DecidableEq V] (σ : WZ) (a b c : V) (l : Fin 2)
    (u v : V × Fin 2) :
    s(u, v) ∈ σ.edges (a, b, c) l ↔
      (joinsAB σ ∧ s(u, v) = s(((a, l) : V × Fin 2), (b, l)))
      ∨ (joinsBC σ ∧ s(u, v) = s(((b, l) : V × Fin 2), (c, l)))
      ∨ (joinsAC σ ∧ s(u, v) = s(((a, l) : V × Fin 2), (c, l))) := by
  cases σ <;>
    simp only [WZ.edges, joinsAB, joinsBC, joinsAC, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, reduceCtorEq, false_or, or_false, true_or, or_true, true_and,
      false_and, and_true, and_false] <;> tauto

-- the mirror forms of Proposition 3.7, also finite checks
lemma prop37_mirror_i : ∀ q : WZExt, WZExt.inLamSq q = true → (WZExt.toPair q).2 = WZ.abc →
    ((WZExt.toPair (WZExt.eta q)).2 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).2 = WZ.ab_c) ∧
    ((WZExt.toPair (WZExt.eta q)).1 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).1 = WZ.ac_b) := by
  decide
lemma prop37_mirror_ii : ∀ q : WZExt, WZExt.inLamSq q = true →
    ((WZExt.toPair q).2 = WZ.abc ∨ (WZExt.toPair q).2 = WZ.ab_c) →
    ((WZExt.toPair (WZExt.eta q)).2 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).2 = WZ.ab_c) := by
  decide
lemma prop37_mirror_iii : ∀ q : WZExt, WZExt.inLamSq q = true →
    ((WZExt.toPair q).2 = WZ.abc ∨ (WZExt.toPair q).2 = WZ.ac_b) →
    ((WZExt.toPair (WZExt.eta q)).1 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).1 = WZ.ac_b) := by
  decide
-- Lambda^2_+ is closed under the level swap
lemma inLamSq_rho : ∀ q : WZExt, WZExt.inLamSq q = true → WZExt.inLamSq (WZExt.rho q) = true := by
  decide
-- inside Lambda^2_+ the state a|bc never occurs, so joinsBC forces abc
lemma no_a_bc : ∀ q : WZExt, WZExt.inLamSq q = true →
    (WZExt.toPair q).1 ≠ WZ.a_bc ∧ (WZExt.toPair q).2 ≠ WZ.a_bc := by decide

lemma htri : ∀ i : Fin 6, hollomTriple i = (hollomTr i, hollomPath i.castSucc, hollomPath i.succ) := by decide

private lemma mem_posts {V : Type*} [Fintype V] [DecidableEq V] (T : Finset V)
    (u v : V × Fin 2) :
    s(u, v) ∈ posts T ↔ u.1 = v.1 ∧ u.1 ∈ T ∧ u.2 ≠ v.2 := by
  obtain ⟨a, i⟩ := u; obtain ⟨b, j⟩ := v
  simp only [posts, mem_image, Sym2.eq_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, (⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ | ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩)⟩ <;> simp_all
  · rintro ⟨rfl, hT, hij⟩
    exact ⟨a, hT, by fin_cases i <;> fin_cases j <;> simp_all⟩

private lemma wzadj {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (t : ι → (V × V × V)) (T : Finset V) (ψ : ι × Fin 2 → WZ)
    (u v : V × Fin 2) :
    (wzGraph t T ψ).Adj u v ↔
      ((∃ p : ι × Fin 2, s(u, v) ∈ (ψ p).edges (t p.1) p.2)
        ∨ (u.1 = v.1 ∧ u.1 ∈ T ∧ u.2 ≠ v.2)) ∧ u ≠ v := by
  rw [wzGraph, ofEdges, fromEdgeSet_adj]
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, mem_biUnion,
    Finset.mem_univ, true_and, mem_posts]


lemma distinct_ab : ∀ i : Fin 6, hollomTr i ≠ hollomPath i.castSucc := by decide
lemma distinct_ac : ∀ i : Fin 6, hollomTr i ≠ hollomPath i.succ := by decide
lemma distinct_bc : ∀ i : Fin 6, hollomPath i.castSucc ≠ hollomPath i.succ := by decide
lemma flip_ne : ∀ l : Fin 2, l ≠ lvlSwap l := by decide

lemma adjAB (ψ : Fin 6 × Fin 2 → WZ) (i : Fin 6) (l : Fin 2) (h : joinsAB (ψ (i, l))) :
    (wzGraph hollomTriple hollomT ψ).Adj (hollomTr i, l) (hollomPath i.castSucc, l) := by
  rw [wzadj]
  refine ⟨Or.inl ⟨(i, l), ?_⟩, ?_⟩
  · rw [mem_edges_iff (a := (hollomTriple i).1) (b := (hollomTriple i).2.1)
        (c := (hollomTriple i).2.2)]
    · exact Or.inl ⟨h, by rw [htri]⟩
  · simp only [ne_eq, Prod.mk.injEq, not_and]
    exact fun hc => absurd hc (distinct_ab i)

lemma adjBC (ψ : Fin 6 × Fin 2 → WZ) (i : Fin 6) (l : Fin 2) (h : joinsBC (ψ (i, l))) :
    (wzGraph hollomTriple hollomT ψ).Adj (hollomPath i.castSucc, l) (hollomPath i.succ, l) := by
  rw [wzadj]
  refine ⟨Or.inl ⟨(i, l), ?_⟩, ?_⟩
  · rw [mem_edges_iff (a := (hollomTriple i).1) (b := (hollomTriple i).2.1)
        (c := (hollomTriple i).2.2)]
    · exact Or.inr (Or.inl ⟨h, by rw [htri]⟩)
  · simp only [ne_eq, Prod.mk.injEq, not_and]
    exact fun hc => absurd hc (distinct_bc i)

lemma adjAC (ψ : Fin 6 × Fin 2 → WZ) (i : Fin 6) (l : Fin 2) (h : joinsAC (ψ (i, l))) :
    (wzGraph hollomTriple hollomT ψ).Adj (hollomTr i, l) (hollomPath i.succ, l) := by
  rw [wzadj]
  refine ⟨Or.inl ⟨(i, l), ?_⟩, ?_⟩
  · rw [mem_edges_iff (a := (hollomTriple i).1) (b := (hollomTriple i).2.1)
        (c := (hollomTriple i).2.2)]
    · exact Or.inr (Or.inr ⟨h, by rw [htri]⟩)
  · simp only [ne_eq, Prod.mk.injEq, not_and]
    exact fun hc => absurd hc (distinct_ac i)

lemma adjPost (ψ : Fin 6 × Fin 2 → WZ) (t : Fin 10) (ht : t ∈ hollomT) (l : Fin 2) :
    (wzGraph hollomTriple hollomT ψ).Adj (t, l) (t, lvlSwap l) := by
  rw [wzadj]
  refine ⟨Or.inr ⟨rfl, ht, flip_ne l⟩, ?_⟩
  simp only [ne_eq, Prod.mk.injEq, not_and]
  exact fun _ => flip_ne l


lemma fmap_tr (e : Fin 6) (i : Fin 6) (l : Fin 2) : surgeryMap e (hollomTr i, l) = (hollomTr i, l) := by
  have : reflected e (hollomTr i) = false := by revert e i; decide
  simp [surgeryMap, this]

lemma fmap_pth_of_lt (e : Fin 6) (j : Fin 7) (hj : e.val < j.val) (l : Fin 2) :
    surgeryMap e (hollomPath j, l) = (hollomPath j, lvlSwap l) := by
  have : reflected e (hollomPath j) = true := by
    simp only [reflected, decide_eq_true_eq]; exact ⟨j, rfl, hj⟩
  simp [surgeryMap, this]

lemma fmap_pth_of_ge (e : Fin 6) (j : Fin 7) (hj : ¬ e.val < j.val) (l : Fin 2) :
    surgeryMap e (hollomPath j, l) = (hollomPath j, l) := by
  have : reflected e (hollomPath j) = false := by
    revert hj; revert e j; decide
  simp [surgeryMap, this]

lemma toPair_rho : ∀ q : WZExt,
    WZExt.toPair (WZExt.rho q) = ((WZExt.toPair q).2, (WZExt.toPair q).1) := by decide

lemma cfg0 (Ψ : Fin 6 → WZExt) (h : Fin 6) : wzOfExt Ψ (h, 0) = (WZExt.toPair (Ψ h)).1 := rfl
lemma cfg1 (Ψ : Fin 6 → WZExt) (h : Fin 6) : wzOfExt Ψ (h, 1) = (WZExt.toPair (Ψ h)).2 := rfl

lemma cfg_lt (e : Fin 6) (Ψ : Fin 6 → WZExt) (h : Fin 6) (hlt : h.val < e.val) (l : Fin 2) :
    wzOfExt (phiExt e Ψ) (h, l) = wzOfExt Ψ (h, l) := by
  simp [wzOfExt, phiExt, hlt]

lemma cfg_gt (e : Fin 6) (Ψ : Fin 6 → WZExt) (h : Fin 6) (hgt : e.val < h.val) (l : Fin 2) :
    wzOfExt (phiExt e Ψ) (h, l) = wzOfExt Ψ (h, lvlSwap l) := by
  have hne : h ≠ e := fun hc => by simp [hc] at hgt
  have hnlt : ¬ h.val < e.val := by omega
  fin_cases l <;>
    simp [wzOfExt, phiExt, hne, hnlt, toPair_rho, lvlSwap]

lemma cfg_eq (e : Fin 6) (Ψ : Fin 6 → WZExt) (l : Fin 2) :
    wzOfExt (phiExt e Ψ) (e, l) = wzOfExt (fun _ => WZExt.eta (Ψ e)) (e, l) := by
  fin_cases l <;> simp [wzOfExt, phiExt]

lemma prop37_i : ∀ q : WZExt, WZExt.inLamSq q = true → (WZExt.toPair q).1 = WZ.abc →
    ((WZExt.toPair (WZExt.eta q)).1 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).1 = WZ.ab_c) ∧
    ((WZExt.toPair (WZExt.eta q)).2 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).2 = WZ.ac_b) := by
  decide
lemma prop37_ii : ∀ q : WZExt, WZExt.inLamSq q = true →
    ((WZExt.toPair q).1 = WZ.abc ∨ (WZExt.toPair q).1 = WZ.ab_c) →
    ((WZExt.toPair (WZExt.eta q)).1 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).1 = WZ.ab_c) := by
  decide
lemma prop37_iii : ∀ q : WZExt, WZExt.inLamSq q = true →
    ((WZExt.toPair q).1 = WZ.abc ∨ (WZExt.toPair q).1 = WZ.ac_b) →
    ((WZExt.toPair (WZExt.eta q)).2 = WZ.abc ∨ (WZExt.toPair (WZExt.eta q)).2 = WZ.ac_b) := by
  decide

lemma tr_mem : ∀ i : Fin 6, hollomTr i ∈ hollomT := by decide

lemma flip0 : lvlSwap 0 = 1 := by decide
lemma flip1 : lvlSwap 1 = 0 := by decide
lemma flipflip : ∀ l : Fin 2, lvlSwap (lvlSwap l) = l := by decide

section
variable (e : Fin 6) (Ψ : Fin 6 → WZExt)

lemma transAB (he : WZExt.inLamSq (Ψ e) = true) (i : Fin 6) (l : Fin 2)
    (h : joinsAB (wzOfExt Ψ (i, l))) :
    (wzGraph hollomTriple hollomT (wzOfExt (phiExt e Ψ))).Reachable (surgeryMap e (hollomTr i, l)) (surgeryMap e (hollomPath i.castSucc, l)) := by
  rw [fmap_tr]
  rcases lt_trichotomy i.val e.val with hlt | heq | hgt
  · rw [fmap_pth_of_ge e i.castSucc (by simp only [Fin.val_castSucc]; omega) l]
    exact (adjAB _ i l (by rw [cfg_lt e Ψ i hlt]; exact h)).reachable
  · have hie : i = e := Fin.ext heq
    rw [hie] at h ⊢
    rw [fmap_pth_of_ge e e.castSucc (by simp only [Fin.val_castSucc]; omega) l]
    refine (adjAB _ e l ?_).reachable
    rw [cfg_eq e Ψ l]
    fin_cases l
    · exact prop37_ii _ he h
    · exact prop37_mirror_ii _ he h
  · rw [fmap_pth_of_lt e i.castSucc (by simp only [Fin.val_castSucc]; omega) l]
    have hstate : joinsAB (wzOfExt (phiExt e Ψ) (i, lvlSwap l)) := by
      rw [cfg_gt e Ψ i hgt, flipflip]; exact h
    exact ((adjPost _ (hollomTr i) (tr_mem i) l).reachable).trans
      (adjAB _ i (lvlSwap l) hstate).reachable

lemma transAC (he : WZExt.inLamSq (Ψ e) = true) (i : Fin 6) (l : Fin 2)
    (h : joinsAC (wzOfExt Ψ (i, l))) :
    (wzGraph hollomTriple hollomT (wzOfExt (phiExt e Ψ))).Reachable (surgeryMap e (hollomTr i, l)) (surgeryMap e (hollomPath i.succ, l)) := by
  rw [fmap_tr]
  rcases lt_trichotomy i.val e.val with hlt | heq | hgt
  · rw [fmap_pth_of_ge e i.succ (by simp only [Fin.val_succ]; omega) l]
    exact (adjAC _ i l (by rw [cfg_lt e Ψ i hlt]; exact h)).reachable
  · have hie : i = e := Fin.ext heq
    rw [hie] at h ⊢
    rw [fmap_pth_of_lt e e.succ (by simp only [Fin.val_succ]; omega) l]
    refine ((adjPost _ (hollomTr e) (tr_mem e) l).reachable).trans
      (adjAC _ e (lvlSwap l) ?_).reachable
    rw [cfg_eq e Ψ (lvlSwap l)]
    fin_cases l
    · exact prop37_iii _ he h
    · exact prop37_mirror_iii _ he h
  · rw [fmap_pth_of_lt e i.succ (by simp only [Fin.val_succ]; omega) l]
    refine ((adjPost _ (hollomTr i) (tr_mem i) l).reachable).trans
      (adjAC _ i (lvlSwap l) ?_).reachable
    rw [cfg_gt e Ψ i hgt, flipflip]; exact h

lemma transBC (he : WZExt.inLamSq (Ψ e) = true) (i : Fin 6) (l : Fin 2)
    (h : joinsBC (wzOfExt Ψ (i, l))) :
    (wzGraph hollomTriple hollomT (wzOfExt (phiExt e Ψ))).Reachable (surgeryMap e (hollomPath i.castSucc, l)) (surgeryMap e (hollomPath i.succ, l)) := by
  rcases lt_trichotomy i.val e.val with hlt | heq | hgt
  · rw [fmap_pth_of_ge e i.castSucc (by simp only [Fin.val_castSucc]; omega) l,
        fmap_pth_of_ge e i.succ (by simp only [Fin.val_succ]; omega) l]
    exact (adjBC _ i l (by rw [cfg_lt e Ψ i hlt]; exact h)).reachable
  · have hie : i = e := Fin.ext heq
    rw [hie] at h ⊢
    rw [fmap_pth_of_ge e e.castSucc (by simp only [Fin.val_castSucc]; omega) l,
        fmap_pth_of_lt e e.succ (by simp only [Fin.val_succ]; omega) l]
    -- inside Lambda^2_+ the state a|bc is absent, so joinsBC forces abc
    have habc : wzOfExt Ψ (e, l) = WZ.abc := by
      rcases h with h1 | h2
      · exact h1
      · exfalso
        fin_cases l
        · exact (no_a_bc _ he).1 (by rw [← cfg0 Ψ e]; exact h2)
        · exact (no_a_bc _ he).2 (by rw [← cfg1 Ψ e]; exact h2)
    fin_cases l
    · obtain ⟨hAB, hAC⟩ := prop37_i _ he habc
      exact ((adjAB _ e 0 (by rw [cfg_eq e Ψ 0]; exact hAB)).reachable.symm).trans
        (((adjPost _ (hollomTr e) (tr_mem e) 0).reachable).trans
          (adjAC _ e 1 (by rw [cfg_eq e Ψ 1]; exact hAC)).reachable)
    · obtain ⟨hAB, hAC⟩ := prop37_mirror_i _ he habc
      exact ((adjAB _ e 1 (by rw [cfg_eq e Ψ 1]; exact hAB)).reachable.symm).trans
        (((adjPost _ (hollomTr e) (tr_mem e) 1).reachable).trans
          (adjAC _ e 0 (by rw [cfg_eq e Ψ 0]; exact hAC)).reachable)
  · rw [fmap_pth_of_lt e i.castSucc (by simp only [Fin.val_castSucc]; omega) l,
        fmap_pth_of_lt e i.succ (by simp only [Fin.val_succ]; omega) l]
    exact (adjBC _ i (lvlSwap l) (by rw [cfg_gt e Ψ i hgt, flipflip]; exact h)).reachable

end

lemma fmap_src : ∀ e : Fin 6, surgeryMap e ((0 : Fin 10), (0 : Fin 2)) = ((0 : Fin 10), (0 : Fin 2)) := by decide
lemma fmap_tgt : ∀ e : Fin 6, surgeryMap e ((9 : Fin 10), (0 : Fin 2)) = ((9 : Fin 10), (1 : Fin 2)) := by decide

lemma swp_T : ∀ (e : Fin 6) (t : Fin 10), t ∈ hollomT → reflected e t = false := by decide
lemma fmap_T (e : Fin 6) (t : Fin 10) (ht : t ∈ hollomT) (l : Fin 2) :
    surgeryMap e (t, l) = (t, l) := by simp [surgeryMap, swp_T e t ht]
lemma fin2_ne : ∀ a b : Fin 2, a ≠ b → b = lvlSwap a := by decide

lemma surgery_edge (e : Fin 6) (Ψ : Fin 6 → WZExt) (he : WZExt.inLamSq (Ψ e) = true)
    (x y : Fin 10 × Fin 2)
    (hadj : (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Adj x y) :
    (wzGraph hollomTriple hollomT (wzOfExt (phiExt e Ψ))).Reachable (surgeryMap e x) (surgeryMap e y) := by
  rw [wzadj] at hadj
  obtain ⟨hor, hne⟩ := hadj
  rcases hor with ⟨⟨i, l⟩, hmem⟩ | ⟨h1, hT, h2⟩
  · rw [htri, mem_edges_iff] at hmem
    rcases hmem with ⟨hj, heq⟩ | ⟨hj, heq⟩ | ⟨hj, heq⟩
    · rcases Sym2.eq_iff.mp heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx, hy]; exact transAB e Ψ he i l hj
      · rw [hx, hy]; exact (transAB e Ψ he i l hj).symm
    · rcases Sym2.eq_iff.mp heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx, hy]; exact transBC e Ψ he i l hj
      · rw [hx, hy]; exact (transBC e Ψ he i l hj).symm
    · rcases Sym2.eq_iff.mp heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx, hy]; exact transAC e Ψ he i l hj
      · rw [hx, hy]; exact (transAC e Ψ he i l hj).symm
  · obtain ⟨xa, xl⟩ := x; obtain ⟨ya, yl⟩ := y
    simp only at h1 h2
    subst h1
    rw [fmap_T e xa hT, fmap_T e xa hT, fin2_ne xl yl h2]
    exact (adjPost _ xa hT xl).reachable

lemma surgery_reach (e : Fin 6) (Ψ : Fin 6 → WZExt) (he : WZExt.inLamSq (Ψ e) = true)
    {x y : Fin 10 × Fin 2}
    (hr : (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable x y) :
    (wzGraph hollomTriple hollomT (wzOfExt (phiExt e Ψ))).Reachable (surgeryMap e x) (surgeryMap e y) := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact Reachable.refl _
  | cons hadj p ih => exact (surgery_edge e Ψ he _ _ hadj).trans ih

/-- **Lemma 3.8.** The involution carries a same-level connection to a cross-level one. -/
theorem solution (e : Fin 6) (Ψ : Fin 6 → WZExt) (he : WZExt.inLamSq (Ψ e) = true)
    (hr : (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
      ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2))) :
    (wzGraph hollomTriple hollomT (wzOfExt (phiExt e Ψ))).Reachable
      ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) := by
  have hres := surgery_reach e Ψ he hr
  rwa [fmap_src e, fmap_tgt e] at hres
