-- Prove2me | solution 1 for FordFulkerson58.ArcChain.labeling_terminates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:41:06.095867+00:00
-- url     : https://prove2.me/submissions/d14c7a2e-9020-4153-979d-fa1166ebee69

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

end FordFulkerson58.ArcChain

open FordFulkerson58.ArcChain


theorem solution {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (S : Finset V) (l : E → ℝ) (hl : ∀ e, 0 ≤ l e) :
    ¬ ∃ f : ℕ → V → WithTop ℝ, f 0 = initLabel S ∧ ∀ i, RelaxStep N l (f i) (f (i + 1)) := by
  exact labeling_terminates_core N S l hl
