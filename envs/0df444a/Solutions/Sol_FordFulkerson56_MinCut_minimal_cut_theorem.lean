-- Prove2me | solution 1 for FordFulkerson56.MinCut.minimal_cut_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T15:38:00.198839+00:00
-- url     : https://prove2.me/submissions/bbf6d0e7-274d-4fb5-b0e3-fb36c3e373bd

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting

set_option linter.unusedSectionVars false

namespace FordFulkerson56.MinCut

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-! ### Flows -/

lemma load_nonneg {f : Finset E → ℝ} (hf : ∀ C, 0 ≤ f C) (e : E) : 0 ≤ load f e :=
  Finset.sum_nonneg fun C _ => hf C

lemma load_linear (a b : ℝ) (f g : Finset E → ℝ) (e : E) :
    load (fun C => a * f C + b * g C) e = a * load f e + b * load g e := by
  simp only [load, Finset.sum_add_distrib, Finset.mul_sum]

lemma value_linear (a b : ℝ) (f g : Finset E → ℝ) :
    value (fun C => a * f C + b * g C) = a * value f + b * value g := by
  simp only [value, Finset.sum_add_distrib, Finset.mul_sum]

/-- Moving `ε` from the chain flow on `C` to the chain flow on `C'`. -/
lemma load_shift (f : Finset E → ℝ) (C C' : Finset E) (ε : ℝ) (e : E) :
    load (fun D => f D - (if D = C then ε else 0) + (if D = C' then ε else 0)) e =
      load f e - (if e ∈ C then ε else 0) + (if e ∈ C' then ε else 0) := by
  simp only [load, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_filter, Finset.mem_univ, true_and]

lemma value_shift (f : Finset E → ℝ) (C C' : Finset E) (ε : ℝ) :
    value (fun D => f D - (if D = C then ε else 0) + (if D = C' then ε else 0)) = value f := by
  simp only [value, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

lemma load_add_single (f : Finset E → ℝ) (C : Finset E) (ε : ℝ) (e : E) :
    load (fun D => f D + (if D = C then ε else 0)) e = load f e + (if e ∈ C then ε else 0) := by
  simp only [load, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and]

lemma value_add_single (f : Finset E → ℝ) (C : Finset E) (ε : ℝ) :
    value (fun D => f D + (if D = C then ε else 0)) = value f + ε := by
  simp only [value, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The null set of arcs is not a chain from the source to the sink. -/
lemma not_isChain_empty (N : Network V E) : ¬ IsChain N N.source N.sink ∅ := by
  rintro ⟨p, vs, ⟨hlen, hhd, hlast, -⟩, hp⟩
  have hp : p = [] := List.toFinset_eq_empty_iff _ |>.mp hp
  subst hp
  match vs, hlen with
  | [x], _ =>
    simp at hhd hlast
    exact N.source_ne_sink (hhd.symm.trans hlast)

lemma isFlow_combo {N : Network V E} {f g : Finset E → ℝ} (hf : IsFlow N f) (hg : IsFlow N g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsFlow N (fun C => a * f C + b * g C) := by
  refine ⟨fun C => add_nonneg (mul_nonneg ha (hf.1 C)) (mul_nonneg hb (hg.1 C)), ?_, ?_⟩
  · intro C hC
    by_cases h : f C = 0
    · by_cases h' : g C = 0
      · simp [h, h'] at hC
      · exact hg.2.1 C h'
    · exact hf.2.1 C h
  · intro e
    rw [load_linear]
    calc a * load f e + b * load g e ≤ a * N.cap e + b * N.cap e := by
          gcongr
          · exact hf.2.2 e
          · exact hg.2.2 e
      _ = N.cap e := by rw [← add_mul, hab, one_mul]

variable [Fintype V] [DecidableEq V]

lemma flow_le_sum_cap {N : Network V E} {f : Finset E → ℝ} (hf : IsFlow N f) (C : Finset E) :
    f C ≤ ∑ e, N.cap e := by
  by_cases hC : C = ∅
  · subst hC
    by_cases h0 : f ∅ = 0
    · rw [h0]; exact Finset.sum_nonneg fun e _ => (N.cap_pos e).le
    · exact absurd (hf.2.1 _ h0) (not_isChain_empty N)
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hC
    calc f C ≤ load f e :=
          Finset.single_le_sum (f := f) (fun D _ => hf.1 D) (by simp [he])
      _ ≤ N.cap e := hf.2.2 e
      _ ≤ ∑ e, N.cap e :=
          Finset.single_le_sum (f := N.cap) (fun e _ => (N.cap_pos e).le) (Finset.mem_univ e)

/-- A maximal flow exists (compactness of the set of flows). -/
lemma exists_isMaxFlow (N : Network V E) : ∃ f, IsMaxFlow N f := by
  classical
  set K := {f : Finset E → ℝ | IsFlow N f} with hKdef
  have hsub : K ⊆ Set.Icc 0 (fun _ => ∑ e, N.cap e) := fun f hf =>
    ⟨fun C => hf.1 C, fun C => flow_le_sum_cap hf C⟩
  have hclosed : IsClosed K := by
    have hK : K = (⋂ C, {f : Finset E → ℝ | 0 ≤ f C}) ∩
        ((⋂ C, {f : Finset E → ℝ | ¬ IsChain N N.source N.sink C → f C = 0}) ∩
          ⋂ e, {f : Finset E → ℝ | load f e ≤ N.cap e}) := by
      ext f
      simp only [hKdef, IsFlow, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, fun C hC => by_contra fun h => hC (h2 C h), h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, fun C hC => by_contra fun h => hC (h2 C h), h3⟩
    rw [hK]
    refine (isClosed_iInter fun C => ?_).inter
      ((isClosed_iInter fun C => ?_).inter (isClosed_iInter fun e => ?_))
    · exact isClosed_le continuous_const (continuous_apply C)
    · by_cases hC : IsChain N N.source N.sink C
      · simp [hC]
      · simp only [hC, not_false_eq_true, true_implies]
        exact isClosed_eq (continuous_apply C) continuous_const
    · exact isClosed_le (continuous_finsetSum _ fun C _ => continuous_apply C) continuous_const
  have hcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hclosed hsub
  have hne : K.Nonempty := ⟨0, fun C => le_rfl, fun C h => absurd rfl h, fun e => by
    simpa [load] using (N.cap_pos e).le⟩
  obtain ⟨f, hfK, hmax⟩ := hcompact.exists_isMaxOn hne
    (continuous_finsetSum _ fun C _ => continuous_apply C).continuousOn
  exact ⟨f, hfK, fun g hg => hmax hg⟩

/-- Weak duality: the value of a flow is at most the value of a disconnecting set. -/
lemma value_le_cutValue {N : Network V E} {f : Finset E → ℝ} (hf : IsFlow N f) {D : Finset E}
    (hD : IsDisconnecting N D) : value f ≤ cutValue N D := by
  calc value f ≤ ∑ C, f C * (C ∩ D).card := by
        refine Finset.sum_le_sum fun C _ => ?_
        by_cases h : f C = 0
        · simp [h]
        · have := (hD C (hf.2.1 C h)).card_pos
          have h1 : (1 : ℝ) ≤ (C ∩ D).card := by exact_mod_cast this
          nlinarith [hf.1 C]
    _ = ∑ e ∈ D, load f e := by
        simp only [load, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum,
          mul_one]
        rw [Finset.sum_comm' (t' := D) (s' := fun e => Finset.univ.filter (fun C => e ∈ C))]
        intro C e
        simp [and_comm]
    _ ≤ cutValue N D := Finset.sum_le_sum fun e _ => hf.2.2 e

end FordFulkerson56.MinCut

namespace FordFulkerson56.MinCut

variable {V E : Type*} [DecidableEq E] {N : Network V E} {u w : V} {p : List E} {vs : List V}

/-! ### Chain walks -/

lemma IsChainWalk.lt_length (h : IsChainWalk N u w p vs) {k : ℕ} (hk : k ≤ p.length) :
    k < vs.length := by
  rw [h.1]; omega

lemma IsChainWalk.getElem_zero (h : IsChainWalk N u w p vs) :
    vs[0]'(h.lt_length (Nat.zero_le _)) = u := by
  have := h.2.1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (h.lt_length (Nat.zero_le _))] at this
  exact Option.some_inj.mp this

lemma IsChainWalk.getElem_last (h : IsChainWalk N u w p vs) :
    vs[p.length]'(h.lt_length le_rfl) = w := by
  have := h.2.2.1
  rw [List.getLast?_eq_getElem?, h.1, Nat.add_sub_cancel,
    List.getElem?_eq_getElem (h.lt_length le_rfl)] at this
  exact Option.some_inj.mp this

lemma IsChainWalk.step (h : IsChainWalk N u w p vs) (i : ℕ) (hi : i < p.length) :
    (vs[i]'(h.lt_length hi.le) = N.tail p[i] ∧ vs[i + 1]'(h.lt_length hi) = N.head p[i]) ∨
    (vs[i]'(h.lt_length hi.le) = N.head p[i] ∧ vs[i + 1]'(h.lt_length hi) = N.tail p[i]) := by
  have h1 := h.lt_length hi.le
  have h2 := h.lt_length hi
  rcases h.2.2.2.2.2 i hi with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [List.getElem?_eq_getElem h1] at ha
    rw [List.getElem?_eq_getElem h2] at hb
    exact Or.inl ⟨Option.some_inj.mp ha, Option.some_inj.mp hb⟩
  · rw [List.getElem?_eq_getElem h1] at ha
    rw [List.getElem?_eq_getElem h2] at hb
    exact Or.inr ⟨Option.some_inj.mp ha, Option.some_inj.mp hb⟩

lemma IsChainWalk.ends_mem (h : IsChainWalk N u w p vs) {e : E} (he : e ∈ p) :
    N.tail e ∈ vs ∧ N.head e ∈ vs := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  rcases h.step i hi with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← ha, ← hb]; exact ⟨List.getElem_mem _, List.getElem_mem _⟩
  · rw [← ha, ← hb]; exact ⟨List.getElem_mem _, List.getElem_mem _⟩

lemma isChainWalk_nil (N : Network V E) (u : V) : IsChainWalk N u u [] [u] := by
  refine ⟨rfl, rfl, rfl, List.nodup_singleton u, List.nodup_nil, fun i hi => ?_⟩
  simp at hi

lemma isChainWalk_single (N : Network V E) {x y : V} {e : E}
    (hxy : (x = N.tail e ∧ y = N.head e) ∨ (x = N.head e ∧ y = N.tail e)) :
    IsChainWalk N x y [e] [x, y] := by
  have hne : x ≠ y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact N.tail_ne_head e
    · exact (N.tail_ne_head e).symm
  refine ⟨rfl, rfl, rfl, by simp [hne], List.nodup_singleton e, fun i hi => ?_⟩
  simp only [List.length_singleton, Nat.lt_one_iff] at hi
  subst hi
  simpa using hxy

lemma IsChainWalk.take (h : IsChainWalk N u w p vs) (k : ℕ) (hk : k ≤ p.length) :
    IsChainWalk N u (vs[k]'(h.lt_length hk)) (p.take k) (vs.take (k + 1)) := by
  have hlen := h.1
  refine ⟨?_, ?_, ?_, h.2.2.2.1.sublist (List.take_sublist _ _),
    h.2.2.2.2.1.sublist (List.take_sublist _ _), fun i hi => ?_⟩
  · simp only [List.length_take]; omega
  · rw [List.head?_take]; simpa using h.2.1
  · rw [List.getLast?_eq_getElem?]
    simp only [List.length_take, List.getElem?_take]
    rw [show min (k + 1) vs.length - 1 = k by omega, if_pos (by omega),
      List.getElem?_eq_getElem (h.lt_length hk)]
  · simp only [List.length_take] at hi
    have := h.2.2.2.2.2 i (by omega)
    simp only [List.getElem?_take, List.getElem_take]
    rw [if_pos (by omega), if_pos (by omega)]
    exact this

lemma IsChainWalk.drop (h : IsChainWalk N u w p vs) (k : ℕ) (hk : k ≤ p.length) :
    IsChainWalk N (vs[k]'(h.lt_length hk)) w (p.drop k) (vs.drop k) := by
  have hlen := h.1
  refine ⟨?_, ?_, ?_, h.2.2.2.1.sublist (List.drop_sublist _ _),
    h.2.2.2.2.1.sublist (List.drop_sublist _ _), fun i hi => ?_⟩
  · simp only [List.length_drop]; omega
  · rw [List.head?_drop, List.getElem?_eq_getElem (h.lt_length hk)]
  · rw [List.getLast?_drop, if_neg (by omega)]; exact h.2.2.1
  · simp only [List.length_drop] at hi
    have := h.2.2.2.2.2 (k + i) (by omega)
    simp only [List.getElem?_drop, List.getElem_drop]
    rw [show k + (i + 1) = k + i + 1 by omega]
    exact this

lemma getElem?_append_tail_left {vs1 vs2 : List V} {i : ℕ} (hi : i < vs1.length) :
    (vs1 ++ vs2.tail)[i]? = vs1[i]? := List.getElem?_append_left hi

lemma getElem?_append_tail_right {vs1 vs2 : List V} {x : V} (hl : vs1.getLast? = some x)
    (hh : vs2.head? = some x) (j : ℕ) :
    (vs1 ++ vs2.tail)[vs1.length - 1 + j]? = vs2[j]? := by
  have hne : vs1 ≠ [] := by rintro rfl; simp at hl
  have hpos : 0 < vs1.length := List.length_pos_iff.mpr hne
  rcases j with _ | j
  · rw [Nat.add_zero, List.getElem?_append_left (by omega), ← List.getLast?_eq_getElem?, hl,
      ← hh, List.head?_eq_getElem?]
  · rw [show vs1.length - 1 + (j + 1) = vs1.length + j by omega,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_tail]

lemma IsChainWalk.append {x : V} {p1 p2 : List E} {vs1 vs2 : List V}
    (h1 : IsChainWalk N u x p1 vs1) (h2 : IsChainWalk N x w p2 vs2)
    (hdisj : ∀ y, y ∈ vs1 → y ∈ vs2 → y = x) :
    IsChainWalk N u w (p1 ++ p2) (vs1 ++ vs2.tail) := by
  have hl1 := h1.1
  have hl2 := h2.1
  -- the vertex sequence of the concatenation
  have hleft : ∀ i, i ≤ p1.length → (vs1 ++ vs2.tail)[i]? = vs1[i]? := fun i hi =>
    getElem?_append_tail_left (by omega)
  have hright : ∀ j, (vs1 ++ vs2.tail)[p1.length + j]? = vs2[j]? := fun j => by
    have := getElem?_append_tail_right (vs2 := vs2) h1.2.2.1 h2.2.1 j
    rwa [hl1, Nat.add_sub_cancel] at this
  have hx2 : vs2.head? = some x := h2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · simp only [List.length_append, List.length_tail]; omega
  · rw [List.head?_append]; simp [h1.2.1]
  · rw [List.getLast?_eq_getElem?]
    have : (vs1 ++ vs2.tail).length - 1 = p1.length + p2.length := by
      simp only [List.length_append, List.length_tail]; omega
    rw [this, hright, List.getElem?_eq_getElem (h2.lt_length le_rfl), h2.getElem_last]
  · rw [List.nodup_append]
    refine ⟨h1.2.2.2.1, h2.2.2.2.1.sublist (List.tail_sublist _), fun a ha b hb hab => ?_⟩
    subst hab
    have hx := hdisj a ha (List.mem_of_mem_tail hb)
    subst hx
    -- `a` is the head of `vs2`, which does not reappear in its tail
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil (show vs2 ≠ [] by rintro rfl; simp at hx2)
    simp only [List.head?_cons, Option.some_inj] at hx2
    subst hx2
    exact (List.nodup_cons.mp h2.2.2.2.1).1 hb
  · rw [List.nodup_append]
    refine ⟨h1.2.2.2.2.1, h2.2.2.2.2.1, fun e he e' he' hee => ?_⟩
    subst hee
    obtain ⟨ht1, hh1⟩ := h1.ends_mem he
    obtain ⟨ht2, hh2⟩ := h2.ends_mem he'
    exact N.tail_ne_head e ((hdisj _ ht1 ht2).trans (hdisj _ hh1 hh2).symm)
  · simp only [List.length_append] at hi
    by_cases hi1 : i < p1.length
    · rw [hleft i hi1.le, hleft (i + 1) hi1, List.getElem_append_left hi1]
      exact h1.2.2.2.2.2 i hi1
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hi1)
      rw [hright j, show p1.length + j + 1 = p1.length + (j + 1) by omega, hright (j + 1),
        List.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      exact h2.2.2.2.2.2 j (by omega)

end FordFulkerson56.MinCut

namespace FordFulkerson56.MinCut

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Arc `e` is saturated by every maximal flow. -/
def SatAll (N : Network V E) (e : E) : Prop := ∀ g, IsMaxFlow N g → Saturated N g e

/-- `v` is reachable from the source by a chain avoiding the arcs saturated by every maximal
flow. -/
def Reach (N : Network V E) (v : V) : Prop :=
  ∃ C, IsChain N N.source v C ∧ ∀ e ∈ C, ¬ SatAll N e

lemma exists_pos_le (A : Finset E) (s : E → ℝ) (hs : ∀ e ∈ A, 0 < s e) :
    ∃ ε > 0, ∀ e ∈ A, ε ≤ s e := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨e₀, he₀, hmin⟩ := A.exists_min_image s hne
    exact ⟨s e₀, hs e₀ he₀, hmin⟩

/-- Averaging maximal flows: for finitely many arcs that are not saturated by every maximal flow,
there is a maximal flow leaving all of them unsaturated, and still dominating a positive multiple of a
given maximal flow. -/
lemma exists_slack (N : Network V E) {f : Finset E → ℝ} (hf : IsMaxFlow N f) (A : Finset E)
    (hA : ∀ e ∈ A, ¬ SatAll N e) :
    ∃ g, IsMaxFlow N g ∧ (∃ c > 0, ∀ C, c * f C ≤ g C) ∧ ∀ e ∈ A, load g e < N.cap e := by
  induction A using Finset.induction_on with
  | empty => exact ⟨f, hf, ⟨1, one_pos, fun C => by simp⟩, by simp⟩
  | insert a A ha ih =>
    obtain ⟨g, hg, ⟨c, hc, hgc⟩, hgA⟩ := ih (fun e he => hA e (Finset.mem_insert_of_mem he))
    have := hA a (Finset.mem_insert_self a A)
    simp only [SatAll, not_forall] at this
    obtain ⟨h, hh, hsat⟩ := this
    have hlt : load h a < N.cap a := lt_of_le_of_ne (hh.1.2.2 a) hsat
    refine ⟨fun C => (1 / 2) * g C + (1 / 2) * h C,
      ⟨isFlow_combo hg.1 hh.1 (by norm_num) (by norm_num) (by norm_num), fun g' hg' => ?_⟩,
      ⟨c / 2, by positivity, fun C => ?_⟩, fun e he => ?_⟩
    · rw [value_linear]
      have := hg.2 g' hg'
      have := hh.2 g' hg'
      linarith
    · have := hgc C
      have := hh.1.1 C
      linarith
    · rw [load_linear]
      rcases Finset.mem_insert.mp he with rfl | he
      · have := hg.1.2.2 e
        linarith
      · have := hgA e he
        have := hh.1.2.2 e
        linarith

/-- Every chain joining the source and the sink contains an arc saturated by every maximal
flow. -/
lemma exists_satAll_of_isChain (N : Network V E) {C : Finset E}
    (hC : IsChain N N.source N.sink C) : ∃ e ∈ C, SatAll N e := by
  by_contra hcon
  push Not at hcon
  obtain ⟨f, hf⟩ := exists_isMaxFlow N
  obtain ⟨g, hg, -, hslack⟩ := exists_slack N hf C hcon
  obtain ⟨ε, hε, hεle⟩ := exists_pos_le C (fun e => N.cap e - load g e)
    (fun e he => sub_pos.mpr (hslack e he))
  have hflow : IsFlow N (fun D => g D + (if D = C then ε else 0)) := by
    refine ⟨fun D => ?_, fun D hD => ?_, fun e => ?_⟩
    · have := hg.1.1 D
      dsimp only
      split_ifs <;> linarith
    · by_cases hDC : D = C
      · subst hDC; exact hC
      · simp only [hDC, if_false, add_zero] at hD
        exact hg.1.2.1 D hD
    · rw [load_add_single]
      split_ifs with he
      · have := hεle e he
        linarith
      · simpa using hg.1.2.2 e
  have := hg.2 _ hflow
  rw [value_add_single] at this
  linarith

lemma reach_source (N : Network V E) : Reach N N.source :=
  ⟨∅, ⟨[], [N.source], isChainWalk_nil N _, rfl⟩, by simp⟩

lemma not_reach_sink (N : Network V E) : ¬ Reach N N.sink := by
  rintro ⟨C, hC, hS⟩
  obtain ⟨e, he, hsat⟩ := exists_satAll_of_isChain N hC
  exact hS e he hsat

/-- Reachability extends along arcs that are not saturated by every maximal flow. -/
lemma reach_of_reach (N : Network V E) {x y : V} {e : E}
    (hxy : (x = N.tail e ∧ y = N.head e) ∨ (x = N.head e ∧ y = N.tail e)) (he : ¬ SatAll N e)
    (hx : Reach N x) : Reach N y := by
  obtain ⟨_, ⟨q, us, hW, rfl⟩, hS⟩ := hx
  by_cases hy : y ∈ us
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hy
    have hk' : k ≤ q.length := by have := hW.1; omega
    refine ⟨_, ⟨_, _, hW.take k hk', rfl⟩, fun e' he' => hS e' ?_⟩
    simp only [List.mem_toFinset] at he' ⊢
    exact List.mem_of_mem_take he'
  · refine ⟨_, ⟨_, _, hW.append (isChainWalk_single N hxy) ?_, rfl⟩, fun e' he' => ?_⟩
    · intro z hz hz'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
      rcases hz' with rfl | rfl
      · rfl
      · exact absurd hz hy
    · simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · exact hS e' (List.mem_toFinset.mpr he')
      · exact he

/-- Along a positive chain flow of a maximal flow, no vertex after an arc saturated by every maximal
flow is reachable. -/
lemma not_reach_after (N : Network V E) {f : Finset E → ℝ} (hf : IsMaxFlow N f) {p : List E}
    {vs : List V} (hpos : f p.toFinset ≠ 0) (hW : IsChainWalk N N.source N.sink p vs) {i : ℕ}
    (hi : i < p.length) (hS : SatAll N p[i]) {j : ℕ} (hij : i < j) (hj : j < vs.length) :
    ¬ Reach N vs[j] := by
  rintro ⟨_, ⟨q, us, hPW, rfl⟩, hPS⟩
  have hlenus := hPW.1
  have hlenvs := hW.1
  -- the first vertex of the reaching chain lying on the remainder of the positive chain
  have hex : ∃ m, ∃ hm : m < us.length, us[m] ∈ vs.drop j :=
    ⟨q.length, by omega, by
      rw [hPW.getElem_last]
      exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩⟩
  classical
  let m := Nat.find hex
  obtain ⟨hm, hmmem⟩ := Nat.find_spec hex
  have hfirst : ∀ k (hk : k < m), us[k]'(by omega) ∉ vs.drop j := fun k hk hmem =>
    Nat.find_min hex hk ⟨by omega, hmem⟩
  obtain ⟨t, ht, hteq⟩ := List.mem_iff_getElem.mp hmmem
  simp only [List.length_drop, List.getElem_drop] at ht hteq
  set j' := j + t with hj'
  have hj'le : j' ≤ p.length := by omega
  have hmq : m ≤ q.length := by omega
  -- the rerouted chain
  have hA := hPW.take m hmq
  have hB := hW.drop j' hj'le
  rw [show vs[j']'(hW.lt_length hj'le) = us[m] from hteq] at hB
  have hW' := hA.append hB (by
    intro y hy hy'
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hy
    simp only [List.length_take, List.getElem_take] at hk hy' ⊢
    by_contra hne
    have hkm : k < m := by
      rcases Nat.lt_or_ge k m with h | h
      · exact h
      · exact absurd (by congr 1; omega) hne
    exact hfirst k hkm ((List.drop_sublist_drop_left vs (by omega : j ≤ j')).subset hy'))
  set C := p.toFinset with hCdef
  set C' := (q.take m ++ p.drop j').toFinset with hC'def
  have hiC : p[i] ∈ C := List.mem_toFinset.mpr (List.getElem_mem _)
  have hiC' : p[i] ∉ C' := by
    simp only [hC'def, List.mem_toFinset, List.mem_append, not_or]
    constructor
    · intro hmem
      exact hPS _ (List.mem_toFinset.mpr (List.mem_of_mem_take hmem)) hS
    · intro hmem
      obtain ⟨r, hr, hreq⟩ := List.mem_iff_getElem.mp hmem
      simp only [List.length_drop, List.getElem_drop] at hr hreq
      have := (List.Nodup.getElem_inj_iff hW.2.2.2.2.1).mp hreq
      omega
  have hCC' : C ≠ C' := fun h => hiC' (h ▸ hiC)
  -- a maximal flow positive on `C` with slack on the reaching chain
  obtain ⟨g, hg, ⟨c, hc, hgc⟩, hslack⟩ := exists_slack N hf q.toFinset hPS
  have hgC : 0 < g C := lt_of_lt_of_le (mul_pos hc (lt_of_le_of_ne (hf.1.1 C) (Ne.symm hpos)))
    (hgc C)
  obtain ⟨ε₀, hε₀, hε₀le⟩ := exists_pos_le q.toFinset (fun e => N.cap e - load g e)
    (fun e he => sub_pos.mpr (hslack e he))
  set ε := min ε₀ (g C) with hεdef
  have hε : 0 < ε := lt_min hε₀ hgC
  set g' : Finset E → ℝ := fun D => g D - (if D = C then ε else 0) + (if D = C' then ε else 0)
    with hg'def
  have hflow : IsFlow N g' := by
    refine ⟨fun D => ?_, fun D hD => ?_, fun e => ?_⟩
    · have := hg.1.1 D
      have : ε ≤ g C := min_le_right _ _
      simp only [hg'def]
      split_ifs with h1 h2 <;> (try subst h1) <;> linarith
    · by_cases h1 : D = C'
      · rw [h1]; exact ⟨_, _, hW', rfl⟩
      · by_cases h2 : D = C
        · rw [h2]; exact ⟨p, vs, hW, rfl⟩
        · simp only [hg'def, h1, h2, if_false, sub_zero, add_zero] at hD
          exact hg.1.2.1 D hD
    · simp only [hg'def]
      rw [load_shift]
      have hle := hg.1.2.2 e
      by_cases h1 : e ∈ C <;> by_cases h2 : e ∈ C' <;> simp only [h1, h2, if_true, if_false]
      · linarith
      · linarith
      · -- `e` lies on the rerouted chain but not on `C`: it is an arc of the reaching chain
        simp only [hC'def, List.mem_toFinset, List.mem_append] at h2
        rcases h2 with h2 | h2
        · have := hε₀le e (List.mem_toFinset.mpr (List.mem_of_mem_take h2))
          have : ε ≤ ε₀ := min_le_left _ _
          linarith
        · exact absurd (List.mem_toFinset.mpr (List.mem_of_mem_drop h2)) h1
      · linarith
  have hmax' : IsMaxFlow N g' := ⟨hflow, fun g'' hg'' => by
    simp only [hg'def]; rw [value_shift]; exact hg.2 g'' hg''⟩
  have := hS g' hmax'
  simp only [Saturated, hg'def] at this
  rw [load_shift, if_pos hiC, if_neg hiC'] at this
  have := hg.1.2.2 p[i]
  linarith

end FordFulkerson56.MinCut

namespace FordFulkerson56.MinCut

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

open Classical in
/-- The arcs with exactly one end reachable. -/
noncomputable def boundary (N : Network V E) : Finset E :=
  Finset.univ.filter fun e => ¬ (Reach N (N.tail e) ↔ Reach N (N.head e))

lemma mem_boundary_iff_of_step (N : Network V E) {e : E} {x y : V}
    (hxy : (x = N.tail e ∧ y = N.head e) ∨ (x = N.head e ∧ y = N.tail e)) :
    e ∈ boundary N ↔ ¬ (Reach N x ↔ Reach N y) := by
  classical
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Iff.rfl
  · exact not_congr iff_comm

lemma satAll_of_mem_boundary (N : Network V E) {e : E} (he : e ∈ boundary N) : SatAll N e := by
  classical
  by_contra hS
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and] at he
  apply he
  exact ⟨reach_of_reach N (Or.inl ⟨rfl, rfl⟩) hS, reach_of_reach N (Or.inr ⟨rfl, rfl⟩) hS⟩

lemma isDisconnecting_boundary (N : Network V E) : IsDisconnecting N (boundary N) := by
  classical
  rintro _ ⟨p, vs, hW, rfl⟩
  have hex : ∃ k, ∃ hk : k < vs.length, ¬ Reach N vs[k] :=
    ⟨p.length, hW.lt_length le_rfl, by rw [hW.getElem_last]; exact not_reach_sink N⟩
  set k := Nat.find hex
  obtain ⟨hk, hnk⟩ := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    have : vs[k] = N.source := by simp only [h0]; exact hW.getElem_zero
    exact hnk (this ▸ reach_source N)
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hlen := hW.1
  have hip : i < p.length := by omega
  have hri : Reach N (vs[i]'(by omega)) := by
    by_contra h
    exact Nat.find_min hex (show i < k by omega) ⟨by omega, h⟩
  refine ⟨p[i], Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem _), ?_⟩⟩
  rw [mem_boundary_iff_of_step N (hW.step i hip)]
  have : vs[i + 1] = vs[k] := by simp only [hi]
  rw [this]
  exact fun h => hnk (h.mp hri)

/-- A positive chain flow of a maximal flow crosses the boundary exactly once. -/
lemma card_inter_boundary (N : Network V E) {f : Finset E → ℝ} (hf : IsMaxFlow N f)
    {C : Finset E} (hpos : f C ≠ 0) : (C ∩ boundary N).card = 1 := by
  classical
  obtain ⟨p, vs, hW, rfl⟩ := hf.1.2.1 C hpos
  have hlen := hW.1
  have hex : ∃ i, ∃ hi : i < p.length, SatAll N p[i] := by
    obtain ⟨e, he, hS⟩ := exists_satAll_of_isChain N ⟨p, vs, hW, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp he)
    exact ⟨i, hi, hS⟩
  set i := Nat.find hex
  obtain ⟨hi, hSi⟩ := Nat.find_spec hex
  -- vertices up to position `i` are reachable, later ones are not
  have hreach : ∀ k (hk : k < vs.length), Reach N vs[k] ↔ k ≤ i := by
    intro k hk
    constructor
    · intro hr
      by_contra hki
      exact not_reach_after N hf hpos hW hi hSi (by omega) hk hr
    · intro hki
      refine ⟨_, ⟨_, _, hW.take k (by omega), rfl⟩, fun e he hS => ?_⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp he)
      simp only [List.length_take, List.getElem_take] at hl hS
      exact Nat.find_min hex (show l < i by omega) ⟨by omega, hS⟩
  have hmem : ∀ k (hk : k < p.length), p[k] ∈ boundary N ↔ k = i := by
    intro k hk
    rw [mem_boundary_iff_of_step N (hW.step k hk), hreach k (by omega), hreach (k + 1) (by omega)]
    omega
  rw [Finset.card_eq_one]
  refine ⟨p[i], Finset.ext fun e => ?_⟩
  simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨he, hb⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    have := (hmem k hk).mp hb
    subst this
    rfl
  · rintro rfl
    exact ⟨List.getElem_mem _, (hmem i hi).mpr rfl⟩

lemma sum_mul_card_inter (f : Finset E → ℝ) (D : Finset E) :
    ∑ C, f C * (C ∩ D).card = ∑ e ∈ D, load f e := by
  simp only [load, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum, mul_one]
  rw [Finset.sum_comm' (t' := D) (s' := fun e => Finset.univ.filter (fun C => e ∈ C))]
  intro C e
  simp [and_comm]

theorem minimal_cut_theorem' (N : Network V E) :
    ∃ m : ℝ, IsGreatest {x : ℝ | ∃ f, IsFlow N f ∧ value f = x} m ∧
      IsLeast {x : ℝ | ∃ D : Finset E, IsDisconnecting N D ∧ cutValue N D = x} m := by
  obtain ⟨f, hf⟩ := exists_isMaxFlow N
  have hval : value f = cutValue N (boundary N) := by
    calc value f = ∑ C, f C * (C ∩ boundary N).card := by
          refine Finset.sum_congr rfl fun C _ => ?_
          by_cases h : f C = 0
          · simp [h]
          · rw [card_inter_boundary N hf h]; simp
      _ = ∑ e ∈ boundary N, load f e := sum_mul_card_inter f _
      _ = cutValue N (boundary N) :=
          Finset.sum_congr rfl fun e he => satAll_of_mem_boundary N he f hf
  refine ⟨value f, ⟨⟨f, hf.1, rfl⟩, ?_⟩, ⟨⟨boundary N, isDisconnecting_boundary N, hval.symm⟩, ?_⟩⟩
  · rintro x ⟨g, hg, rfl⟩
    exact hf.2 g hg
  · rintro x ⟨D, hD, rfl⟩
    exact hval ▸ (value_le_cutValue hf.1 hD).trans_eq rfl |>.trans_eq' hval.symm

end FordFulkerson56.MinCut

open FordFulkerson56.MinCut

theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : Network V E) :
    ∃ m : ℝ, IsGreatest {x : ℝ | ∃ f, IsFlow N f ∧ value f = x} m ∧
      IsLeast {x : ℝ | ∃ D : Finset E, IsDisconnecting N D ∧ cutValue N D = x} m :=
  minimal_cut_theorem' N
