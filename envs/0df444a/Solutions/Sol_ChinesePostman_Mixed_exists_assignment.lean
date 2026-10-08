-- Prove2me | solution 1 for ChinesePostman.Mixed.exists_assignment
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:27:21.892619+00:00
-- url     : https://prove2.me/submissions/1ccb94c2-e093-44aa-9de1-548cb2004f68

import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting



namespace ChinesePostman.Mixed

theorem eo_aux {V E : Type} [DecidableEq V] [DecidableEq E] :
    ∀ (m : ℕ) (F : Finset E) (t h : E → V), F.card = m →
    (∀ n, Even (∑ e ∈ F, ((if t e = n then 1 else 0) + (if h e = n then 1 else 0) : ℕ))) →
    ∃ src dst : E → V,
      (∀ e ∈ F, (src e = t e ∧ dst e = h e) ∨ (src e = h e ∧ dst e = t e)) ∧
      ∀ n, ∑ e ∈ F, (if src e = n then 1 else 0 : ℕ) = ∑ e ∈ F, (if dst e = n then 1 else 0 : ℕ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F t h hcard hev
  by_cases hF : F = ∅
  · subst hF
    exact ⟨t, h, by simp, by simp⟩
  obtain ⟨e1, he1⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  by_cases hloop : t e1 = h e1
  · -- remove loop
    obtain ⟨src, dst, hv, hb⟩ := ih (F.erase e1).card (by rw [← hcard]; exact Finset.card_erase_lt_of_mem he1)
      (F.erase e1) t h rfl (by
        intro n
        have := hev n
        rw [← Finset.add_sum_erase F _ he1] at this
        have h2 : (if t e1 = n then 1 else 0 : ℕ) + (if h e1 = n then 1 else 0) =
            2 * (if t e1 = n then 1 else 0) := by rw [← hloop]; ring
        rw [h2] at this
        exact ((Nat.even_add.mp this).mp (even_two_mul _)))
    refine ⟨fun e => if e = e1 then t e1 else src e, fun e => if e = e1 then h e1 else dst e, ?_, ?_⟩
    · intro e he
      by_cases hee : e = e1
      · subst hee; simp
      · simp only [hee, if_false]; exact hv e (Finset.mem_erase.mpr ⟨hee, he⟩)
    · intro n
      rw [← Finset.add_sum_erase F _ he1, ← Finset.add_sum_erase F (fun e => if (if e = e1 then h e1 else dst e) = n then 1 else 0) he1]
      have k1 : ∀ e ∈ F.erase e1, (if (if e = e1 then t e1 else src e) = n then 1 else 0 : ℕ) = (if src e = n then 1 else 0) := by
        intro e he; simp [Finset.ne_of_mem_erase he]
      have k2 : ∀ e ∈ F.erase e1, (if (if e = e1 then h e1 else dst e) = n then 1 else 0 : ℕ) = (if dst e = n then 1 else 0) := by
        intro e he; simp [Finset.ne_of_mem_erase he]
      rw [Finset.sum_congr rfl k1, Finset.sum_congr rfl k2, hb n]
      simp [hloop]
  · -- general step
    set b := h e1 with hb
    set a := t e1 with ha
    have hab : t e1 ≠ b := hloop
    have hodd : ¬ Even (∑ e ∈ F.erase e1, ((if t e = b then 1 else 0) + (if h e = b then 1 else 0) : ℕ)) := by
      have := hev b
      rw [← Finset.add_sum_erase F _ he1] at this
      have h1 : (if t e1 = b then 1 else 0 : ℕ) + (if h e1 = b then 1 else 0) = 1 := by
        rw [if_neg hab, if_pos hb.symm]
      rw [h1] at this
      intro hc
      rw [Nat.even_add] at this
      simp at this
      exact absurd hc (by simpa using this)
    obtain ⟨e2, he2, hodd2⟩ : ∃ e2 ∈ F.erase e1, ¬ Even ((if t e2 = b then 1 else 0) + (if h e2 = b then 1 else 0) : ℕ) := by
      by_contra hcon
      push_neg at hcon
      exact hodd (Finset.even_sum _ (fun e he => by simpa using hcon e he))
    have he2F : e2 ∈ F := Finset.mem_of_mem_erase he2
    have hne21 : e2 ≠ e1 := Finset.ne_of_mem_erase he2
    -- the other end c of e2
    obtain ⟨c, hc⟩ : ∃ c, (t e2 = b ∧ h e2 = c) ∨ (h e2 = b ∧ t e2 = c) := by
      by_cases ht : t e2 = b
      · exact ⟨h e2, Or.inl ⟨ht, rfl⟩⟩
      · by_cases hh : h e2 = b
        · exact ⟨t e2, Or.inr ⟨hh, rfl⟩⟩
        · exfalso; apply hodd2; simp [ht, hh]
    have hdeg2 : ∀ n, (if t e2 = n then 1 else 0 : ℕ) + (if h e2 = n then 1 else 0) =
        (if b = n then 1 else 0) + (if c = n then 1 else 0) := by
      intro n
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]; ring
    set R := (F.erase e1).erase e2 with hR
    have hRc : F.card = R.card + 2 := by
      rw [hR, Finset.card_erase_of_mem he2, Finset.card_erase_of_mem he1]
      have : 0 < (F.erase e1).card := Finset.card_pos.mpr ⟨e2, he2⟩
      have : (F.erase e1).card = F.card - 1 := Finset.card_erase_of_mem he1
      have : 0 < F.card := Finset.card_pos.mpr ⟨e1, he1⟩
      omega
    set h' : E → V := fun e => if e = e1 then c else h e with hh'
    set F' := F.erase e2 with hF'
    have he1F' : e1 ∈ F' := Finset.mem_erase.mpr ⟨hne21.symm, he1⟩
    have hF'R : F'.erase e1 = R := by
      rw [hF', hR]; exact Finset.erase_right_comm
    have hsumF : ∀ f : E → ℕ, ∑ e ∈ F, f e = f e1 + f e2 + ∑ e ∈ R, f e := by
      intro f
      rw [← Finset.add_sum_erase F f he1, ← Finset.add_sum_erase (F.erase e1) f he2]
      ring
    have hsumF' : ∀ f : E → ℕ, ∑ e ∈ F', f e = f e1 + ∑ e ∈ R, f e := by
      intro f
      rw [← Finset.add_sum_erase F' f he1F', hF'R]
    have hRh : ∀ e ∈ R, h' e = h e := by
      intro e he
      have : e ≠ e1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he)
      simp [hh', this]
    obtain ⟨src, dst, hv, hbal⟩ := ih F'.card (by
        rw [← hcard]; exact Finset.card_erase_lt_of_mem he2F) F' t h' rfl (by
      intro n
      have := hev n
      rw [hsumF] at this
      rw [hsumF']
      have hRsum : ∑ e ∈ R, ((if t e = n then 1 else 0) + (if h' e = n then 1 else 0) : ℕ) =
          ∑ e ∈ R, ((if t e = n then 1 else 0) + (if h e = n then 1 else 0) : ℕ) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hRh e he]
      rw [hRsum]
      rw [hdeg2 n] at this
      have h1' : h' e1 = c := by simp [hh']
      rw [h1']
      have e3 : (if t e1 = n then 1 else 0 : ℕ) + (if h e1 = n then 1 else 0) + ((if b = n then 1 else 0) + (if c = n then 1 else 0)) =
          ((if t e1 = n then 1 else 0 : ℕ) + (if c = n then 1 else 0)) + 2 * (if b = n then 1 else 0) := by
        rw [← hb]; ring
      have key : ((if t e1 = n then 1 else 0 : ℕ) + (if h e1 = n then 1 else 0) + ((if b = n then 1 else 0) + (if c = n then 1 else 0)))
          + ∑ e ∈ R, ((if t e = n then 1 else 0) + (if h e = n then 1 else 0) : ℕ) =
          (((if t e1 = n then 1 else 0 : ℕ) + (if c = n then 1 else 0)) + ∑ e ∈ R, ((if t e = n then 1 else 0) + (if h e = n then 1 else 0) : ℕ)) + 2 * (if b = n then 1 else 0) := by
        rw [e3]; ring
      rw [key] at this
      exact (Nat.even_add.mp this).mpr (even_two_mul _))
    have hRmem : ∀ e ∈ R, e ≠ e1 ∧ e ≠ e2 ∧ e ∈ F' := by
      intro e he
      have h2 : e ≠ e2 := Finset.ne_of_mem_erase he
      have h3 := Finset.mem_of_mem_erase he
      exact ⟨Finset.ne_of_mem_erase h3, h2, Finset.mem_erase.mpr ⟨h2, Finset.mem_of_mem_erase h3⟩⟩
    have hv1 := hv e1 he1F'
    have h1' : h' e1 = c := by simp [hh']
    rw [h1'] at hv1
    have hF'eq : ∀ e ∈ F, e ≠ e1 → e ≠ e2 → (src e = t e ∧ dst e = h e) ∨ (src e = h e ∧ dst e = t e) := by
      intro e he h1 h2
      have := hv e (Finset.mem_erase.mpr ⟨h2, he⟩)
      simpa [hh', h1] using this
    have hbal1 := fun n => by
      have := hbal n
      rw [hsumF', hsumF'] at this
      exact this
    by_cases hA : src e1 = t e1 ∧ dst e1 = c
    · refine ⟨fun e => if e = e1 then t e1 else if e = e2 then b else src e,
              fun e => if e = e1 then b else if e = e2 then c else dst e, ?_, ?_⟩
      · intro e he
        by_cases h1 : e = e1
        · subst h1; simp [hb]
        · by_cases h2 : e = e2
          · subst h2
            rcases hc with ⟨k1, k2⟩ | ⟨k1, k2⟩
            · simp [h1, k1, k2]
            · simp [h1, k1, k2]
          · simp only [h1, h2, if_false]; exact hF'eq e he h1 h2
      · intro n
        rw [hsumF (fun e => if (if e = e1 then t e1 else if e = e2 then b else src e) = n then 1 else 0),
          hsumF (fun e => if (if e = e1 then b else if e = e2 then c else dst e) = n then 1 else 0)]
        have c1 : ∑ e ∈ R, (if (if e = e1 then t e1 else if e = e2 then b else src e) = n then 1 else 0 : ℕ) =
            ∑ e ∈ R, (if src e = n then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl; intro e he
          obtain ⟨k1, k2, _⟩ := hRmem e he
          simp [k1, k2]
        have c2 : ∑ e ∈ R, (if (if e = e1 then b else if e = e2 then c else dst e) = n then 1 else 0 : ℕ) =
            ∑ e ∈ R, (if dst e = n then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl; intro e he
          obtain ⟨k1, k2, _⟩ := hRmem e he
          simp [k1, k2]
        rw [c1, c2]
        have := hbal1 n
        rw [hA.1, hA.2] at this
        simp only [if_true, hne21, if_false]
        omega
    · have hB : src e1 = c ∧ dst e1 = t e1 := by
        rcases hv1 with h | h
        · exact absurd h hA
        · exact h
      refine ⟨fun e => if e = e1 then b else if e = e2 then c else src e,
              fun e => if e = e1 then t e1 else if e = e2 then b else dst e, ?_, ?_⟩
      · intro e he
        by_cases h1 : e = e1
        · subst h1; simp [hb]
        · by_cases h2 : e = e2
          · subst h2
            rcases hc with ⟨k1, k2⟩ | ⟨k1, k2⟩
            · simp [h1, k1, k2]
            · simp [h1, k1, k2]
          · simp only [h1, h2, if_false]; exact hF'eq e he h1 h2
      · intro n
        rw [hsumF (fun e => if (if e = e1 then b else if e = e2 then c else src e) = n then 1 else 0),
          hsumF (fun e => if (if e = e1 then t e1 else if e = e2 then b else dst e) = n then 1 else 0)]
        have c1 : ∑ e ∈ R, (if (if e = e1 then b else if e = e2 then c else src e) = n then 1 else 0 : ℕ) =
            ∑ e ∈ R, (if src e = n then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl; intro e he
          obtain ⟨k1, k2, _⟩ := hRmem e he
          simp [k1, k2]
        have c2 : ∑ e ∈ R, (if (if e = e1 then t e1 else if e = e2 then b else dst e) = n then 1 else 0 : ℕ) =
            ∑ e ∈ R, (if dst e = n then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl; intro e he
          obtain ⟨k1, k2, _⟩ := hRmem e he
          simp [k1, k2]
        rw [c1, c2]
        have := hbal1 n
        rw [hB.1, hB.2] at this
        simp only [if_true, hne21, if_false]
        omega

theorem degree_decomp {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : MixedGraph V E) (n : V) :
    G.degree n = G.outDeg n + G.inDeg n + G.undirDeg n := by
  unfold MixedGraph.degree MixedGraph.outDeg MixedGraph.inDeg MixedGraph.undirDeg
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hl := G.loopless e
  cases hd : G.directed e <;> by_cases h1 : G.tail e = n <;> by_cases h2 : G.head e = n <;>
    simp [h1, h2] <;> (first | omega | (subst h1; exact absurd h2.symm hl))

theorem exists_assignment_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hconn : G.Connected) (heven : G.IsEven)
    (hsym : G.IsSymmetric) :
    ∃ G' : MixedGraph V E,
      (∀ e, s(G'.tail e, G'.head e) = s(G.tail e, G.head e)) ∧
      (∀ e, G.directed e = true →
        G'.directed e = true ∧ G'.tail e = G.tail e ∧ G'.head e = G.head e) ∧
      G'.IsSymmetric ∧ G'.DirectedConnected ∧ (∀ n, Even (G'.undirDeg n)) := by
  classical
  have hund : ∀ n, Even (G.undirDeg n) := by
    intro n
    have h1 := heven n
    rw [degree_decomp, hsym n] at h1
    have : G.inDeg n + G.inDeg n + G.undirDeg n = 2 * G.inDeg n + G.undirDeg n := by ring
    rw [this] at h1
    exact (Nat.even_add.mp h1).mp (even_two_mul _)
  have hevF : ∀ n, Even (∑ e ∈ Finset.univ.filter (fun e => G.directed e = false),
      ((if G.tail e = n then 1 else 0) + (if G.head e = n then 1 else 0) : ℕ)) := by
    intro n
    have : ∑ e ∈ Finset.univ.filter (fun e => G.directed e = false),
      ((if G.tail e = n then 1 else 0) + (if G.head e = n then 1 else 0) : ℕ) = G.undirDeg n := by
      unfold MixedGraph.undirDeg
      rw [Finset.card_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      have hl := G.loopless e
      by_cases hd : G.directed e = false
      · simp only [hd, if_true]
        by_cases h1 : G.tail e = n <;> by_cases h2 : G.head e = n <;> simp [h1, h2]
        subst h1; exact absurd h2.symm hl
      · simp [hd]
    rw [this]; exact hund n
  obtain ⟨src, dst, hv, hb⟩ := eo_aux _ (Finset.univ.filter (fun e => G.directed e = false))
    G.tail G.head rfl hevF
  have hvall : ∀ e, G.directed e = false → (src e = G.tail e ∧ dst e = G.head e) ∨
      (src e = G.head e ∧ dst e = G.tail e) := by
    intro e he
    exact hv e (by simpa using he)
  let G' : MixedGraph V E :=
    { tail := fun e => if G.directed e = true then G.tail e else src e
      head := fun e => if G.directed e = true then G.head e else dst e
      directed := fun _ => true
      loopless := by
        intro e
        by_cases hd : G.directed e = true
        · simp only [hd, if_true]; exact G.loopless e
        · have hd' : G.directed e = false := by simpa using hd
          simp only [hd, if_false]
          have hl := G.loopless e
          rcases hvall e hd' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact hl
          · rw [h1, h2]; exact hl.symm }
  have hsame : ∀ e, s(G'.tail e, G'.head e) = s(G.tail e, G.head e) := by
    intro e
    by_cases hd : G.directed e = true
    · simp [G', hd]
    · have hd' : G.directed e = false := by simpa using hd
      have ht : G'.tail e = src e := by simp [G', hd']
      have hh : G'.head e = dst e := by simp [G', hd']
      rw [ht, hh]
      rcases hvall e hd' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, Sym2.eq_swap]
  refine ⟨G', hsame, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp [G', he]
  · -- symmetric
    intro n
    have hF : ∀ f : E → V, ∑ e : E, (if G.directed e = false ∧ f e = n then 1 else 0 : ℕ) =
        ∑ e ∈ Finset.univ.filter (fun e => G.directed e = false), (if f e = n then 1 else 0 : ℕ) := by
      intro f
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hd : G.directed e = false <;> simp [hd]
    have hout : G'.outDeg n = G.outDeg n + ∑ e ∈ Finset.univ.filter (fun e => G.directed e = false), (if src e = n then 1 else 0 : ℕ) := by
      rw [← hF src]
      unfold MixedGraph.outDeg
      simp only [Finset.card_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hd : G.directed e = true
      · simp [G', hd]
      · have hd' : G.directed e = false := by simpa using hd
        simp [G', hd, hd']
    have hin : G'.inDeg n = G.inDeg n + ∑ e ∈ Finset.univ.filter (fun e => G.directed e = false), (if dst e = n then 1 else 0 : ℕ) := by
      rw [← hF dst]
      unfold MixedGraph.inDeg
      simp only [Finset.card_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hd : G.directed e = true
      · simp [G', hd]
      · have hd' : G.directed e = false := by simpa using hd
        simp [G', hd, hd']
    rw [hout, hin, hsym n, hb n]
  · -- directed connected
    intro i j
    obtain ⟨ns, es, ⟨hlen, hw⟩, hhead, hlast⟩ := hconn i j
    refine ⟨ns, es, ⟨hlen, ?_⟩, hhead, hlast⟩
    intro k hk
    refine ⟨rfl, ?_⟩
    obtain ⟨_, hor⟩ := hw k hk
    have := hsame es[k]
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at this
      rcases Sym2.eq_iff.mp this with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl ⟨a, b⟩
      · exact Or.inr ⟨a, b⟩
    · rw [h1, h2] at this
      rcases Sym2.eq_iff.mp this with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inr ⟨a, b⟩
      · exact Or.inl ⟨a, b⟩
  · intro n
    have : G'.undirDeg n = 0 := by
      unfold MixedGraph.undirDeg
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e _ h
      exact absurd h.1 (by simp [G'])
    rw [this]; exact ⟨0, rfl⟩

end ChinesePostman.Mixed

open ChinesePostman.Mixed


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hconn : G.Connected) (heven : G.IsEven)
    (hsym : G.IsSymmetric) :
    ∃ G' : MixedGraph V E,
      (∀ e, s(G'.tail e, G'.head e) = s(G.tail e, G.head e)) ∧
      (∀ e, G.directed e = true →
        G'.directed e = true ∧ G'.tail e = G.tail e ∧ G'.head e = G.head e) ∧
      G'.IsSymmetric ∧ G'.DirectedConnected ∧ (∀ n, Even (G'.undirDeg n)) := by
  exact exists_assignment_core G hconn heven hsym
