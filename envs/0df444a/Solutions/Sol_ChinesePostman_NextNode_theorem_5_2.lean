-- Prove2me | solution 1 for ChinesePostman.NextNode.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:57:53.904723+00:00
-- url     : https://prove2.me/submissions/646231ed-22ed-4463-b163-ac5bf13c847e

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting



namespace ChinesePostman.NextNode

def usedDeg {V E : Type} [DecidableEq V] [DecidableEq E] (G : Graph V E) (U : Finset E) (a : V) : ℕ :=
  (U.filter (fun f => a ∈ G.ends f)).card

def cntU {V E : Type} [DecidableEq V] [DecidableEq E] (G : Graph V E) (U : Finset E) (a b : V) : ℕ :=
  (U.filter (fun f => G.ends f = s(a, b))).card

lemma usedDeg_insert {V E : Type} [DecidableEq V] [DecidableEq E] (G : Graph V E) (U : Finset E) (e : E)
    (hnot : e ∉ U) (a : V) :
    usedDeg G (insert e U) a = usedDeg G U a + (if a ∈ G.ends e then 1 else 0) := by
  unfold usedDeg
  rw [Finset.filter_insert]
  by_cases h : a ∈ G.ends e
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp [hnot])]
  · rw [if_neg h, if_neg h]; rfl

lemma cntU_insert {V E : Type} [DecidableEq V] [DecidableEq E] (G : Graph V E) (U : Finset E) (e : E)
    (hnot : e ∉ U) (a b : V) :
    cntU G (insert e U) a b = cntU G U a b + (if G.ends e = s(a, b) then 1 else 0) := by
  unfold cntU
  rw [Finset.filter_insert]
  by_cases h : G.ends e = s(a, b)
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp [hnot])]
  · rw [if_neg h, if_neg h]; rfl

lemma upd_count {V : Type} [DecidableEq V] (L : V → List V) (m n x y : V) :
    (Function.update L m (L m ++ [n]) x).count y = (L x).count y + (if x = m ∧ n = y then 1 else 0) := by
  by_cases hx : x = m
  · subst hx
    simp only [Function.update_self, List.count_append, List.count_singleton, true_and]
    by_cases h : n = y <;> simp [h]
  · simp [Function.update_of_ne hx, hx]

lemma upd_length {V : Type} [DecidableEq V] (L : V → List V) (m n x : V) :
    (Function.update L m (L m ++ [n]) x).length = (L x).length + (if x = m then 1 else 0) := by
  by_cases hx : x = m
  · subst hx; simp
  · simp [Function.update_of_ne hx, hx]

lemma parent_upd {V : Type} [DecidableEq V] (r : V) (L : V → List V) (m n y : V)
    (hy : y ≠ r) (hL : L y ≠ []) :
    parent r (Function.update L m (L m ++ [n])) y = parent r L y := by
  unfold parent
  rw [if_neg hy, if_neg hy]
  by_cases h : y = m
  · subst h
    obtain ⟨x, l, hx⟩ : ∃ x l, L y = x :: l := by
      cases hh : L y with
      | nil => exact absurd hh hL
      | cons x l => exact ⟨x, l, rfl⟩
    simp [hx]
  · simp [Function.update_of_ne h]

lemma reach_preserve {V : Type} [DecidableEq V] (r : V) (L L' : V → List V)
    (H : ∀ y, y ≠ r → L y ≠ [] → parent r L' y = parent r L y) :
    ∀ (j : ℕ) (x : V), (parent r L)^[j] x = r → (parent r L')^[j] x = r := by
  intro j
  induction j with
  | zero => intro x hx; simpa using hx
  | succ j ih =>
    intro x hx
    by_cases hxr : x = r
    · subst hxr
      have h1 : parent x L' x = x := by simp [parent]
      exact Function.iterate_fixed h1 _
    · by_cases hL : L x = []
      · exfalso
        have h1 : parent r L x = x := by simp [parent, hxr, hL]
        have := Function.iterate_fixed h1 (j + 1)
        exact hxr (this.symm.trans hx)
      · rw [Function.iterate_succ_apply] at hx ⊢
        rw [H x hxr hL]
        exact ih _ hx

lemma step_facts {V E : Type} [DecidableEq V] [DecidableEq E] (G : Graph V E) (r n0 n m : V) (e : E)
    (used : Finset E) (L : V → List V)
    (hm : G.ends e = s(n, m)) (hnot : e ∉ used)
    (hI1 : ∀ a b, cntU G used a b = (L a).count b + (L b).count a)
    (hI2 : ∀ a, usedDeg G used a + (if a = n then 1 else 0) = 2 * (L a).length + (if a = n0 then 1 else 0))
    (hI3 : ∀ f ∈ used, ∀ x ∈ G.ends f, x = r ∨ L x ≠ [])
    (hI4 : n = r ∨ L n ≠ [])
    (hI5 : ∀ x, (x = r ∨ L x ≠ []) → ∃ j, (parent r L)^[j] x = r) :
    (∀ a b, cntU G (insert e used) a b =
      ((Function.update L m (L m ++ [n])) a).count b + ((Function.update L m (L m ++ [n])) b).count a) ∧
    (∀ a, usedDeg G (insert e used) a + (if a = m then 1 else 0) =
      2 * ((Function.update L m (L m ++ [n])) a).length + (if a = n0 then 1 else 0)) ∧
    (∀ f ∈ insert e used, ∀ x ∈ G.ends f, x = r ∨ (Function.update L m (L m ++ [n])) x ≠ []) ∧
    (∀ x, (x = r ∨ (Function.update L m (L m ++ [n])) x ≠ []) →
      ∃ j, (parent r (Function.update L m (L m ++ [n])))^[j] x = r) := by
  have hnm : n ≠ m := by
    intro h
    apply G.loopless e
    rw [hm, h]; exact Sym2.mk_isDiag_iff.2 rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    rw [cntU_insert G used e hnot, hI1, upd_count, upd_count, hm]
    by_cases h1 : s(n, m) = s(a, b)
    · rw [if_pos h1]
      rw [Sym2.eq_iff] at h1
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [hnm, hnm.symm]; omega
      · simp [hnm, hnm.symm]; omega
    · rw [if_neg h1]
      have h2 : ¬ (a = m ∧ n = b) := by
        rintro ⟨h2a, h2b⟩; exact h1 (by rw [Sym2.eq_iff]; right; exact ⟨h2b, h2a.symm⟩)
      have h3 : ¬ (b = m ∧ n = a) := by
        rintro ⟨h3a, h3b⟩; exact h1 (by rw [Sym2.eq_iff]; left; exact ⟨h3b, h3a.symm⟩)
      simp [h2, h3]
  · intro a
    rw [usedDeg_insert G used e hnot, hm, upd_length]
    have := hI2 a
    by_cases ha : a = m
    · subst ha
      have : a ≠ n := hnm.symm
      simp [Sym2.mem_iff, this] at *
      omega
    · by_cases han : a = n
      · subst han
        simp [Sym2.mem_iff, ha] at *
        omega
      · simp [Sym2.mem_iff, ha, han] at *
        omega
  · intro f hf x hx
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · rw [hm, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · by_cases hxm : x = m
        · right; subst hxm; simp
        · rcases hI4 with h | h
          · left; exact h
          · right; simpa [Function.update_of_ne hxm] using h
      · right; simp
    · rcases hI3 f hf x hx with h | h
      · left; exact h
      · right
        by_cases hxm : x = m
        · subst hxm; simp
        · simpa [Function.update_of_ne hxm] using h
  · intro x hx
    have hH : ∀ y, y ≠ r → L y ≠ [] → parent r (Function.update L m (L m ++ [n])) y = parent r L y :=
      fun y hy hL => parent_upd r L m n y hy hL
    by_cases hxr : x = r
    · exact ⟨0, by simpa using hxr⟩
    · have hx1 : Function.update L m (L m ++ [n]) x ≠ [] := hx.resolve_left hxr
      by_cases hxm : x = m
      · subst hxm
        by_cases hLx : L x = []
        · have hpar : parent r (Function.update L x (L x ++ [n])) x = n := by
            simp [parent, hxr, hLx]
          obtain ⟨j, hj⟩ := hI5 n hI4
          refine ⟨j + 1, ?_⟩
          rw [Function.iterate_succ_apply, hpar]
          exact reach_preserve r L _ hH j n hj
        · obtain ⟨j, hj⟩ := hI5 x (Or.inr hLx)
          exact ⟨j, reach_preserve r L _ hH j x hj⟩
      · have hLx : L x ≠ [] := by simpa [Function.update_of_ne hxm] using hx1
        obtain ⟨j, hj⟩ := hI5 x (Or.inr hLx)
        exact ⟨j, reach_preserve r L _ hH j x hj⟩

def AlgInv {V E : Type} [DecidableEq V] [DecidableEq E] (G : Graph V E) (r n0 n : V) (e : E)
    (used : Finset E) (L : V → List V) : Prop :=
  e ∉ used ∧
  (∀ a b, cntU G used a b = (L a).count b + (L b).count a) ∧
  (∀ a, usedDeg G used a + (if a = n then 1 else 0) = 2 * (L a).length + (if a = n0 then 1 else 0)) ∧
  (∀ f ∈ used, ∀ x ∈ G.ends f, x = r ∨ L x ≠ []) ∧
  (n = r ∨ L n ≠ []) ∧
  (∀ x, (x = r ∨ L x ≠ []) → ∃ j, (parent r L)^[j] x = r)

def AlgOK {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E] (G : Graph V E) (r : V) :
    AlgState V E → Prop
  | .step1 n0 n e used L => AlgInv G r n0 n e used L
  | .done L => CondI G L ∧ CondII G L ∧ CondIII G r L

lemma stuck_eq {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E] (G : Graph V E)
    (heven : ∀ n, Even (degree G n)) (n0 m : V) (U : Finset E) (L1 : V → List V)
    (hF2 : ∀ a, usedDeg G U a + (if a = m then 1 else 0) = 2 * (L1 a).length + (if a = n0 then 1 else 0))
    (hstuck : ∀ f, m ∈ G.ends f → f ∈ U) : m = n0 := by
  have h1 : usedDeg G U m = degree G m := by
    unfold usedDeg degree
    congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hstuck f h, h⟩⟩
  have h2 := hF2 m
  obtain ⟨k, hk⟩ := heven m
  by_contra hne
  simp [hne] at h2
  omega

lemma exists_mem_sym2 {V : Type} (z : Sym2 V) : ∃ x, x ∈ z := by
  induction z using Sym2.ind with
  | h x y => exact ⟨x, Sym2.mem_mk_left x y⟩

lemma all_used {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E] (G : Graph V E)
    (hconn : Connected G) (U : Finset E) (e : E) (he : e ∈ U)
    (hnone : ∀ v, (∃ f ∈ U, v ∈ G.ends f) → ∀ f, v ∈ G.ends f → f ∈ U) : U = Finset.univ := by
  ext f
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨x, hx⟩ := exists_mem_sym2 (G.ends e)
  obtain ⟨y, hy⟩ := exists_mem_sym2 (G.ends f)
  obtain ⟨ns, es, hw, hh, hl⟩ := hconn x y
  obtain ⟨hlen, hwe⟩ := hw
  have key : ∀ i (hi : i < ns.length), ∃ g ∈ U, ns[i] ∈ G.ends g := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨e, he, ?_⟩
      have : ns[0] = x := by
        cases ns with
        | nil => simp at hi
        | cons a l => simpa using hh
      rw [this]; exact hx
    | succ i ih =>
      intro hi
      obtain h1 := ih (by omega)
      have hes : i < es.length := by omega
      have hend := hwe i hes
      have hmem : ns[i] ∈ G.ends es[i] := by rw [hend]; exact Sym2.mem_mk_left _ _
      have hU : es[i] ∈ U := hnone _ h1 _ hmem
      refine ⟨es[i], hU, ?_⟩
      rw [hend]; exact Sym2.mem_mk_right _ _
  have hlast : ns[ns.length - 1]'(by omega) = y := by
    rw [List.getLast?_eq_getElem?] at hl
    have : ns[ns.length - 1]? = some (ns[ns.length - 1]'(by omega)) := List.getElem?_eq_getElem (by omega)
    rw [this] at hl
    exact Option.some.inj hl
  obtain h1 := key (ns.length - 1) (by omega)
  rw [hlast] at h1
  exact hnone y h1 f hy

lemma exists_edge_at {V E : Type} [DecidableEq V] (G : Graph V E) (hconn : Connected G) (n r : V)
    (hn : n ≠ r) : ∃ f, n ∈ G.ends f := by
  obtain ⟨ns', es', hw, hh, hl⟩ := hconn n r
  have hes : es' ≠ [] := by
    intro he
    obtain ⟨hlen, _⟩ := hw
    rw [he] at hlen
    match ns', hlen, hh, hl with
    | [x], _, hh, hl => simp at hh hl; exact hn (hh.symm.trans hl)
  have h0 : 0 < es'.length := List.length_pos_iff.2 hes
  have hlen := hw.1
  have := hw.2 0 h0
  have hn0 : ns'[0]'(by omega) = n := by
    cases ns' with
    | nil => simp at hlen
    | cons x xs => simpa using hh
  rw [hn0] at this
  exact ⟨es'[0], by rw [this]; exact Sym2.mem_mk_left _ _⟩

lemma final_facts {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype E] (G : Graph V E)
    (hconn : Connected G) (r : V) (L1 : V → List V)
    (hall : ∀ a, usedDeg G Finset.univ a = 2 * (L1 a).length)
    (hF1 : ∀ a b, cntU G Finset.univ a b = (L1 a).count b + (L1 b).count a)
    (hF3 : ∀ f ∈ (Finset.univ : Finset E), ∀ x ∈ G.ends f, x = r ∨ L1 x ≠ [])
    (hF5 : ∀ x, (x = r ∨ L1 x ≠ []) → ∃ j, (parent r L1)^[j] x = r) :
    CondI G L1 ∧ CondII G L1 ∧ CondIII G r L1 := by
  have hI : CondI G L1 := by
    intro n
    have := hall n
    unfold usedDeg at this
    unfold degree
    exact this.symm
  have hII : CondII G L1 := by
    intro n m
    have := hF1 n m
    unfold cntU at this
    unfold edgeCount
    omega
  have hne : ∀ n, n ≠ r → L1 n ≠ [] := by
    intro n hn
    obtain ⟨f, hf⟩ := exists_edge_at G hconn n r hn
    rcases hF3 f (Finset.mem_univ _) n hf with h | h
    · exact absurd h hn
    · exact h
  refine ⟨hI, hII, hne, ?_, ?_⟩
  · intro n hn
    obtain ⟨x, l, hx⟩ : ∃ x l, L1 n = x :: l := by
      cases hh : L1 n with
      | nil => exact absurd hh (hne n hn)
      | cons x l => exact ⟨x, l, rfl⟩
    have h1 := hII n x
    have hc : 0 < (L1 n).count x := by rw [hx]; simp
    have : 0 < edgeCount G n x := by omega
    unfold edgeCount at this
    obtain ⟨f, hf⟩ := Finset.card_pos.1 this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact ⟨f, by simp [hx, hf]⟩
  · intro n
    by_cases hn : n = r
    · exact ⟨0, by simpa using hn⟩
    · exact hF5 n (Or.inr (hne n hn))

theorem alg_ok {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hconn : Connected G) (heven : ∀ n, Even (degree G n)) (r : V) (e₀ : E)
    (hr : r ∈ G.ends e₀) (s : AlgState V E)
    (hs : Relation.ReflTransGen (AlgStep G) (.step1 r r e₀ ∅ (fun _ => [])) s) : AlgOK G r s := by
  induction hs with
  | refl =>
    refine ⟨by simp, ?_, ?_, ?_, Or.inl rfl, ?_⟩
    · intro a b; simp [cntU]
    · intro a; simp [usedDeg]
    · intro f hf; simp at hf
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨0, rfl⟩
      · exact absurd rfl hx
  | tail _ hstep ih =>
    cases hstep with
    | step2 n0 n m e e' used L hm he' hme' =>
      obtain ⟨hnot, hI1, hI2, hI3, hI4, hI5⟩ := ih
      obtain ⟨F1, F2, F3, F5⟩ := step_facts G r n0 n m e used L hm hnot hI1 hI2 hI3 hI4 hI5
      exact ⟨he', F1, F2, F3, Or.inr (by simp), F5⟩
    | step3 n0 n m n0' e e' used L hm hstuck hused he' hn0e' =>
      obtain ⟨hnot, hI1, hI2, hI3, hI4, hI5⟩ := ih
      obtain ⟨F1, F2, F3, F5⟩ := step_facts G r n0 n m e used L hm hnot hI1 hI2 hI3 hI4 hI5
      have hmn0 : m = n0 := stuck_eq G heven n0 m _ _ F2 hstuck
      subst hmn0
      refine ⟨he', F1, ?_, F3, ?_, F5⟩
      · intro a
        have := F2 a
        omega
      · obtain ⟨f, hf, hxf⟩ := hused
        exact F3 f hf n0' hxf
    | stop n0 n m e used L hm hstuck hnone =>
      obtain ⟨hnot, hI1, hI2, hI3, hI4, hI5⟩ := ih
      obtain ⟨F1, F2, F3, F5⟩ := step_facts G r n0 n m e used L hm hnot hI1 hI2 hI3 hI4 hI5
      have hmn0 : m = n0 := stuck_eq G heven n0 m _ _ F2 hstuck
      subst hmn0
      have huniv := all_used G hconn _ e (Finset.mem_insert_self _ _) hnone
      rw [huniv] at F1 F2 F3
      refine final_facts G hconn r _ ?_ F1 F3 F5
      intro a
      have := F2 a
      omega

theorem theorem_5_2_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hconn : Connected G) (heven : ∀ n, Even (degree G n)) (r : V) (e₀ : E)
    (hr : r ∈ G.ends e₀) (L : V → List V) (hL : AlgProduces G r e₀ L) :
    CondI G L ∧ CondII G L ∧ CondIII G r L :=
  alg_ok G hconn heven r e₀ hr (.done L) hL

end ChinesePostman.NextNode

open ChinesePostman.NextNode


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ChinesePostman.NextNode.Graph V E) (hconn : Connected G) (heven : ∀ n, Even (degree G n)) (r : V) (e₀ : E)
    (hr : r ∈ G.ends e₀) (L : V → List V) (hL : AlgProduces G r e₀ L) :
    CondI G L ∧ CondII G L ∧ CondIII G r L := by
  exact theorem_5_2_core G hconn heven r e₀ hr L hL
