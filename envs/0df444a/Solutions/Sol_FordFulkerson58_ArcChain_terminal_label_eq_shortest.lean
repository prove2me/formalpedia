-- Prove2me | solution 1 for FordFulkerson58.ArcChain.terminal_label_eq_shortest
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:43:45.000978+00:00
-- url     : https://prove2.me/submissions/dc757a82-3607-4b7d-a131-33ee526ccd54

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_Labeling



namespace FordFulkerson58.ArcChain

variable {V E ι : Type*}

def plen (l : E → ℝ) (p : List E) : ℝ := (p.map l).sum

def PrefOK (l : E → ℝ) (lab : V → WithTop ℝ) (p : List E) (vs : List V) : Prop :=
  ∀ (i : ℕ) (x : V), vs[i]? = some x → lab x ≤ ((plen l (p.take i) : ℝ) : WithTop ℝ)

def Inv [DecidableEq V] (N : Network V E ι) (l : E → ℝ) (S : Finset V) (lab : V → WithTop ℝ) : Prop :=
  (∀ v ∈ S, lab v ≤ 0) ∧ ∀ v, lab v ≠ ⊤ → ∃ (u : V) (p : List E) (vs : List V), u ∈ S ∧
    IsChainWalk N u v p vs ∧ lab v = ((plen l p : ℝ) : WithTop ℝ) ∧ PrefOK l lab p vs

lemma plen_nil (l : E → ℝ) : plen l [] = 0 := by simp [plen]

lemma plen_append_single (l : E → ℝ) (p : List E) (e : E) : plen l (p ++ [e]) = plen l p + l e := by
  simp [plen]

lemma plen_take_le (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) (p : List E) (i : ℕ) :
    plen l (p.take i) ≤ plen l p := by
  have h : plen l p = plen l (p.take i) + plen l (p.drop i) := by
    unfold plen; rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  have : 0 ≤ plen l (p.drop i) := by
    unfold plen
    apply List.sum_nonneg
    intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
    exact hl a
  linarith

lemma traverses_mem {N : Network V E ι} {e : E} {a b x y : V} (h1 : Traverses N e a b)
    (h2 : Traverses N e x y) : b = x ∨ b = y := by
  unfold Traverses at h1 h2
  rcases h1 with ⟨h1, h1'⟩ | ⟨h0, h1, h1'⟩ <;> rcases h2 with ⟨h2, h2'⟩ | ⟨h0', h2, h2'⟩ <;>
    subst_vars <;> simp_all

lemma relax_le [DecidableEq V] {N : Network V E ι} {l : E → ℝ} {lab lab' : V → WithTop ℝ}
    (h : RelaxStep N l lab lab') (x : V) : lab' x ≤ lab x := by
  obtain ⟨e, u, v, _, hlt, rfl⟩ := h
  by_cases hx : x = v
  · subst hx; simp [hlt.le]
  · simp [Function.update_of_ne hx]

lemma inv_init [DecidableEq V] (N : Network V E ι) (l : E → ℝ) (S : Finset V) :
    Inv N l S (initLabel S) := by
  refine ⟨fun v hv => by simp [initLabel, hv], ?_⟩
  intro v hv
  have hvS : v ∈ S := by
    by_contra h; simp [initLabel, h] at hv
  refine ⟨v, [], [v], hvS, ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩, ?_, ?_⟩
  · simp [initLabel, hvS, plen_nil]
  · intro i x hx
    cases i with
    | zero =>
      simp at hx; subst hx; simp [initLabel, hvS, plen_nil]
    | succ i => simp at hx

lemma inv_step [DecidableEq V] {N : Network V E ι} {l : E → ℝ} (hl : ∀ e, 0 ≤ l e) {S : Finset V}
    {lab lab' : V → WithTop ℝ} (hI : Inv N l S lab) (hs : RelaxStep N l lab lab') :
    Inv N l S lab' := by
  have hle := relax_le hs
  obtain ⟨e, u, v, hT, hlt, rfl⟩ := hs
  refine ⟨fun w hw => (hle w).trans (hI.1 w hw), ?_⟩
  intro w hw
  by_cases hwv : w = v
  · subst hwv
    have hu : lab u ≠ ⊤ := by
      intro h; rw [h] at hlt; simp at hlt
    obtain ⟨u0, p, vs, hu0, hwalk, hlu, hpref⟩ := hI.2 u hu
    have hvvs : w ∉ vs := by
      intro hmem
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
      have h1 := hpref i w hi
      have h2 : ((plen l (p.take i) : ℝ) : WithTop ℝ) ≤ ((plen l p : ℝ) : WithTop ℝ) :=
        WithTop.coe_le_coe.2 (plen_take_le l hl p i)
      have h3 : ((plen l p : ℝ) : WithTop ℝ) ≤ lab u + ((l e : ℝ) : WithTop ℝ) := by
        rw [hlu, ← WithTop.coe_add]; exact WithTop.coe_le_coe.2 (by linarith [hl e])
      exact absurd (h1.trans (h2.trans h3)) (not_le.2 hlt)
    have hep : e ∉ p := by
      intro hep
      obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 hep
      obtain ⟨x, y, hx, hy, hxy⟩ := hwalk.2.2.2.2.2 i hi
      rw [hie] at hxy
      rcases traverses_mem hT hxy with h | h
      · exact hvvs (List.mem_iff_getElem?.2 ⟨i, h ▸ hx⟩)
      · exact hvvs (List.mem_iff_getElem?.2 ⟨i+1, h ▸ hy⟩)
    obtain ⟨hlen, hhead, hlast, hnd, hpnd, harc⟩ := hwalk
    have hne : vs ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen
    refine ⟨u0, p ++ [e], vs ++ [w], hu0, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [hlen]
    · rw [List.head?_append]; simp [hhead]
    · simp
    · simp only [List.nodup_append, hnd, List.nodup_singleton, true_and]
      intro a ha b hb; simp at hb; subst hb; intro h; subst h; exact hvvs ha
    · simp only [List.nodup_append, hpnd, List.nodup_singleton, true_and]
      intro a ha b hb; simp at hb; subst hb; intro h; subst h; exact hep ha
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hip : i < p.length
      · obtain ⟨x, y, hx, hy, hxy⟩ := harc i hip
        refine ⟨x, y, ?_, ?_, ?_⟩
        · rw [List.getElem?_append_left (by omega)]; exact hx
        · rw [List.getElem?_append_left (by omega)]; exact hy
        · rwa [List.getElem_append_left hip]
      · have hi' : i = p.length := by omega
        subst hi'
        have hvl : vs[p.length]? = some u := by
          rw [List.getLast?_eq_getElem?] at hlast
          have : vs.length - 1 = p.length := by omega
          rwa [this] at hlast
        refine ⟨u, w, ?_, ?_, ?_⟩
        · rw [List.getElem?_append_left (by omega)]; exact hvl
        · rw [List.getElem?_append_right (by omega)]; simp [hlen]
        · simpa using hT
    · simp only [Function.update_self]
      rw [hlu, plen_append_single, WithTop.coe_add]
    · intro i x hx
      by_cases hiv : i < vs.length
      · rw [List.getElem?_append_left hiv] at hx
        have : (p ++ [e]).take i = p.take i := List.take_append_of_le_length (by omega)
        rw [this]
        exact (hle x).trans (hpref i x hx)
      · have hi' : i = vs.length := by
          by_contra hne'
          rw [List.getElem?_append_right (by omega)] at hx
          have : i - vs.length ≠ 0 := by omega
          simp [this] at hx
        subst hi'
        rw [List.getElem?_append_right (by omega)] at hx
        simp at hx; subst hx
        have : (p ++ [e]).take vs.length = p ++ [e] := List.take_of_length_le (by simp [hlen])
        rw [this, plen_append_single, WithTop.coe_add, ← hlu]
        simp
  · rw [Function.update_of_ne hwv] at hw
    obtain ⟨u0, p, vs, hu0, hwalk, hlw, hpref⟩ := hI.2 w hw
    refine ⟨u0, p, vs, hu0, hwalk, ?_, ?_⟩
    · rw [Function.update_of_ne hwv]; exact hlw
    · intro i x hx
      exact (hle x).trans (hpref i x hx)

lemma inv_of_run [DecidableEq V] {N : Network V E ι} {l : E → ℝ} (hl : ∀ e, 0 ≤ l e) {S : Finset V}
    {lab : V → WithTop ℝ} (h : Relation.ReflTransGen (RelaxStep N l) (initLabel S) lab) :
    Inv N l S lab := by
  induction h with
  | refl => exact inv_init N l S
  | tail _ hs ih => exact inv_step hl ih hs


lemma chainLength_toFinset [DecidableEq E] (l : E → ℝ) {p : List E} (h : p.Nodup) :
    chainLength l p.toFinset = plen l p := by
  unfold chainLength plen
  exact List.sum_toFinset l h

theorem labeling_terminates_core {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) :
    ¬ ∃ f : ℕ → V → WithTop ℝ, f 0 = initLabel S ∧ ∀ i, RelaxStep N l (f i) (f (i + 1)) := by
  rintro ⟨f, h0, hf⟩
  have hrun : ∀ i, Relation.ReflTransGen (RelaxStep N l) (initLabel S) (f i) := by
    intro i
    induction i with
    | zero => rw [h0]
    | succ i ih => exact ih.tail (hf i)
  let F : Set (WithTop ℝ) := insert ⊤ (Set.range (fun C : Finset E => ((chainLength l C : ℝ) : WithTop ℝ)))
  have hF : F.Finite := (Set.finite_range _).insert _
  have hmem : ∀ i, f i ∈ Set.pi Set.univ (fun _ : V => F) := by
    intro i v _
    by_cases h : f i v = ⊤
    · exact Or.inl h
    · obtain ⟨u, p, vs, _, hw, hlab, _⟩ := (inv_of_run hl (hrun i)).2 v h
      right
      exact ⟨p.toFinset, by show ((chainLength l p.toFinset : ℝ) : WithTop ℝ) = _; rw [chainLength_toFinset l hw.2.2.2.2.1, hlab]⟩
  have hfin : (Set.pi Set.univ (fun _ : V => F)).Finite := Set.Finite.pi (fun _ => hF)
  have hanti : StrictAnti f := by
    apply strictAnti_nat_of_succ_lt
    intro i
    refine lt_of_le_of_ne (fun v => relax_le (hf i) v) ?_
    intro heq
    obtain ⟨e, u, v, _, hlt, hup⟩ := hf i
    have := congrFun heq v
    rw [hup] at this
    simp at this
    rw [this] at hlt
    exact lt_irrefl _ hlt
  have hinf : (Set.range f).Infinite := Set.infinite_range_of_injective hanti.injective
  exact hinf (hfin.subset (by rintro _ ⟨i, rfl⟩; exact hmem i))


lemma plen_take_succ (l : E → ℝ) (p : List E) (i : ℕ) (h : i < p.length) :
    plen l (p.take (i + 1)) = plen l (p.take i) + l p[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  unfold plen
  rw [Option.toList_some, List.map_append, List.sum_append]
  simp

lemma lab_le_walk [DecidableEq V] {N : Network V E ι} {l : E → ℝ} {S : Finset V}
    {lab : V → WithTop ℝ} (hS : ∀ v ∈ S, lab v ≤ 0) (hterm : IsTerminal N l lab)
    {u w : V} {p : List E} {vs : List V} (hu : u ∈ S) (hw : IsChainWalk N u w p vs) :
    lab w ≤ ((plen l p : ℝ) : WithTop ℝ) := by
  obtain ⟨hlen, hhead, hlast, hnd, hpnd, harc⟩ := hw
  have key : ∀ (i : ℕ) (x : V), vs[i]? = some x → lab x ≤ ((plen l (p.take i) : ℝ) : WithTop ℝ) := by
    intro i
    induction i with
    | zero =>
      intro x hx
      have : vs.head? = some x := by rw [List.head?_eq_getElem?]; exact hx
      rw [hhead] at this
      have hx' : u = x := Option.some.inj this
      subst hx'
      simpa [plen_nil] using hS u hu
    | succ i ih =>
      intro y hy
      have hi : i < p.length := by
        have := (List.getElem?_eq_some_iff.1 hy).1
        omega
      obtain ⟨x, y', hx, hy', hxy⟩ := harc i hi
      rw [hy] at hy'
      have hyy : y = y' := Option.some.inj hy'
      subst hyy
      have h1 := ih x hx
      have h2 := hterm _ _ _ hxy
      rw [plen_take_succ l p i hi]
      calc lab y ≤ lab x + ((l p[i] : ℝ) : WithTop ℝ) := h2
        _ ≤ ((plen l (p.take i) : ℝ) : WithTop ℝ) + ((l p[i] : ℝ) : WithTop ℝ) := add_le_add h1 le_rfl
        _ = _ := by rw [← WithTop.coe_add]
  have := key p.length w (by
    rw [List.getLast?_eq_getElem?] at hlast
    have e : vs.length - 1 = p.length := by omega
    rwa [e] at hlast)
  simpa using this

lemma tight_claim [DecidableEq V] {N : Network V E ι} {l : E → ℝ} {lab : V → WithTop ℝ}
    {u v : V} {p : List E} {vs : List V} (hw : IsChainWalk N u v p vs)
    (hv : lab v = ((plen l p : ℝ) : WithTop ℝ)) (hpref : PrefOK l lab p vs)
    (hterm : IsTerminal N l lab) :
    ∀ (k i : ℕ), i + k = p.length → ∀ x, vs[i]? = some x →
      lab x = ((plen l (p.take i) : ℝ) : WithTop ℝ) := by
  obtain ⟨hlen, hhead, hlast, hnd, hpnd, harc⟩ := hw
  intro k
  induction k with
  | zero =>
    intro i hi x hx
    have hi' : i = p.length := by omega
    subst hi'
    rw [List.getLast?_eq_getElem?] at hlast
    have e : vs.length - 1 = p.length := by omega
    rw [e, hx] at hlast
    have : x = v := Option.some.inj hlast
    subst this
    simpa using hv
  | succ k ih =>
    intro i hi x hx
    have hip : i < p.length := by omega
    obtain ⟨x', y, hx', hy, hxy⟩ := harc i hip
    rw [hx] at hx'
    have : x = x' := Option.some.inj hx'
    subst this
    have hly := ih (i + 1) (by omega) y hy
    have h1 := hpref i x hx
    have h2 := hterm _ _ _ hxy
    rw [hly, plen_take_succ l p i hip] at h2
    generalize lab x = a at h1 h2 ⊢
    have ha : a ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h1
    lift a to ℝ using ha
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h2
    rw [WithTop.coe_le_coe] at h1
    rw [WithTop.coe_inj]
    linarith


lemma lab_le_chain [DecidableEq V] [DecidableEq E] {N : Network V E ι} {l : E → ℝ} {S : Finset V}
    {lab : V → WithTop ℝ} (hS : ∀ v ∈ S, lab v ≤ 0) (hterm : IsTerminal N l lab)
    {w : V} {C : Finset E} (hC : IsChainFrom N S w C) :
    lab w ≤ ((chainLength l C : ℝ) : WithTop ℝ) := by
  obtain ⟨u, hu, p, vs, hw, rfl⟩ := hC
  rw [chainLength_toFinset l hw.2.2.2.2.1]
  exact lab_le_walk hS hterm hu hw

theorem terminal_label_eq_shortest_core {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S T : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) (lab : V → WithTop ℝ)
    (hrun : Relation.ReflTransGen (RelaxStep N l) (initLabel S) lab) (hterm : IsTerminal N l lab) :
    (∀ v, lab v = shortestChainLength N l S v) ∧ T.inf lab = shortestChainLengthTo N l S T := by
  classical
  have hI := inv_of_run hl hrun
  have h1 : ∀ v, lab v = shortestChainLength N l S v := by
    intro v
    unfold shortestChainLength
    apply le_antisymm
    · apply Finset.le_inf
      intro C hC
      exact lab_le_chain hI.1 hterm (Finset.mem_filter.1 hC).2
    · by_cases hv : lab v = ⊤
      · rw [hv]; exact le_top
      · obtain ⟨u, p, vs, hu, hw, hlab, _⟩ := hI.2 v hv
        have hCmem : p.toFinset ∈ (Finset.univ : Finset (Finset E)).filter (fun C => IsChainFrom N S v C) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨u, hu, p, vs, hw, rfl⟩⟩
        have := Finset.inf_le (f := fun C => ((chainLength l C : ℝ) : WithTop ℝ)) hCmem
        rw [chainLength_toFinset l hw.2.2.2.2.1] at this
        rw [hlab]; exact this
  refine ⟨h1, ?_⟩
  unfold shortestChainLengthTo
  apply le_antisymm
  · apply Finset.le_inf
    intro C hC
    obtain ⟨t, ht, hCt⟩ := (Finset.mem_filter.1 hC).2
    exact (Finset.inf_le ht).trans (lab_le_chain hI.1 hterm hCt)
  · apply Finset.le_inf
    intro t ht
    rw [h1 t]
    unfold shortestChainLength
    apply Finset.inf_mono
    intro C hC
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, t, ht, (Finset.mem_filter.1 hC).2⟩

theorem exists_tight_chain_core {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) (lab : V → WithTop ℝ)
    (hrun : Relation.ReflTransGen (RelaxStep N l) (initLabel S) lab) (hterm : IsTerminal N l lab)
    (v : V) (hv : lab v ≠ ⊤) :
    (v ∉ S → ∃ (e : E) (u : V), Traverses N e u v ∧ lab u + (l e : WithTop ℝ) = lab v) ∧
    ∃ u ∈ S, ∃ (p : List E) (vs : List V), IsChainWalk N u v p vs ∧
      (∀ (i : ℕ) (h : i < p.length), ∃ x y : V, vs[i]? = some x ∧ vs[i + 1]? = some y ∧
        lab y = lab x + (l p[i] : WithTop ℝ)) ∧
      ((chainLength l p.toFinset : ℝ) : WithTop ℝ) = lab v := by
  have hI := inv_of_run hl hrun
  obtain ⟨u, p, vs, hu, hw, hlab, hpref⟩ := hI.2 v hv
  have tc := tight_claim hw hlab hpref hterm
  have hstep : ∀ (i : ℕ) (h : i < p.length), ∃ x y : V, vs[i]? = some x ∧ vs[i + 1]? = some y ∧
      Traverses N p[i] x y ∧ lab y = lab x + (l p[i] : WithTop ℝ) := by
    intro i h
    obtain ⟨x, y, hx, hy, hxy⟩ := hw.2.2.2.2.2 i h
    refine ⟨x, y, hx, hy, hxy, ?_⟩
    rw [tc (p.length - i) i (by omega) x hx, tc (p.length - (i + 1)) (i + 1) (by omega) y hy,
      plen_take_succ l p i h, WithTop.coe_add]
  refine ⟨?_, u, hu, p, vs, hw, ?_, ?_⟩
  · intro hvS
    have hp : p ≠ [] := by
      intro hp
      subst hp
      obtain ⟨hlen, hhead, hlast, _⟩ := hw
      have : vs = [u] := by
        match vs, hlen, hhead with
        | [a], _, hh => simp at hh; simp [hh]
      subst this
      simp at hlast; subst hlast; exact hvS hu
    have hpos : 0 < p.length := List.length_pos_iff.2 hp
    obtain ⟨x, y, hx, hy, hxy, heq⟩ := hstep (p.length - 1) (by omega)
    have hlast := hw.2.2.1
    rw [List.getLast?_eq_getElem?] at hlast
    have e1 : vs.length - 1 = p.length := by have := hw.1; omega
    have e2 : p.length - 1 + 1 = p.length := by omega
    rw [e2] at hy
    rw [e1, hy] at hlast
    have : y = v := Option.some.inj hlast
    subst this
    exact ⟨_, x, hxy, heq.symm⟩
  · intro i h
    obtain ⟨x, y, hx, hy, _, heq⟩ := hstep i h
    exact ⟨x, y, hx, hy, heq⟩
  · rw [chainLength_toFinset l hw.2.2.2.2.1, hlab]

end FordFulkerson58.ArcChain

open FordFulkerson58.ArcChain


theorem solution {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S T : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) (lab : V → WithTop ℝ)
    (hrun : Relation.ReflTransGen (RelaxStep N l) (initLabel S) lab) (hterm : IsTerminal N l lab) :
    (∀ v, lab v = shortestChainLength N l S v) ∧ T.inf lab = shortestChainLengthTo N l S T := by
  exact terminal_label_eq_shortest_core N S T l hl lab hrun hterm
