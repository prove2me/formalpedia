-- Prove2me | solution 1 for BulteauTranspositions.NPHard.property_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:22:00.872691+00:00
-- url     : https://prove2.me/submissions/3d898b1f-9de3-4277-af0a-cc5f1b12c341

import Definitions.Def_BulteauTranspositions_NPHard_Blocks

namespace Aux_BulteauTranspositions_NPHard_property_13

open BulteauTranspositions.NPHard

theorem tau_cases (c : Cut) (y : ℕ) :
    (y < c.i ∧ c.tau y = y) ∨
    (c.i ≤ y ∧ y < c.k + c.i - c.j ∧ c.tau y = y + c.j - c.i) ∨
    (c.i ≤ y ∧ c.k + c.i - c.j ≤ y ∧ y < c.k ∧ c.tau y = y + c.j - c.k) ∨
    (c.i ≤ y ∧ c.k + c.i - c.j ≤ y ∧ c.k ≤ y ∧ c.tau y = y) := by
  unfold Cut.tau
  split_ifs <;> omega

theorem inv_i (c : Cut) : c.inv.i = c.i := rfl
theorem inv_j (c : Cut) : c.inv.j = c.k + c.i - c.j := rfl
theorem inv_k (c : Cut) : c.inv.k = c.k := rfl

theorem tau_inv_cases (c : Cut) (h1 : c.i < c.j) (h2 : c.j < c.k) (x : ℕ) :
    (x < c.i ∧ c.inv.tau x = x) ∨
    (c.i ≤ x ∧ x < c.j ∧ c.inv.tau x = x + c.k - c.j) ∨
    (c.j ≤ x ∧ x < c.k ∧ c.inv.tau x + c.j = x + c.i) ∨
    (c.k ≤ x ∧ c.inv.tau x = x) := by
  have A := tau_cases c.inv x
  rw [inv_i, inv_j, inv_k] at A
  generalize c.inv.tau x = y at A ⊢
  omega

theorem tau_iff (c : Cut) (h1 : c.i < c.j) (h2 : c.j < c.k) (s p Q : ℕ)
    (H1 : ¬ (c.i ≤ s ∧ s < c.j ∧ c.j ≤ p ∧ p < c.k))
    (H2 : ¬ (c.i ≤ p ∧ p < c.j ∧ c.j ≤ s ∧ s < c.k)) (hQ : Q = p) :
    c.inv.tau s < c.inv.tau p ↔ s < Q := by
  have A := tau_inv_cases c h1 h2 s
  have B := tau_inv_cases c h1 h2 p
  constructor <;> intro <;> omega

theorem tau_iff_b (c : Cut) (h1 : c.i < c.j) (h2 : c.j < c.k) (s pb px py pz : ℕ)
    (hcase : (c.i = px ∧ c.j = py ∧ c.k = pz) ∨ (c.i = pz ∧ c.j = px ∧ c.k = py))
    (hb1 : px < pb) (hb2 : pb < py) (hs : ¬ (px ≤ s ∧ s < py)) :
    c.inv.tau s < c.inv.tau pb ↔ s < pz := by
  have A := tau_inv_cases c h1 h2 s
  have B := tau_inv_cases c h1 h2 pb
  constructor <;> intro <;> omega

def cnt (l : List ℕ) (p : ℕ) : ℕ := (l.filter (fun s => decide (s < p))).length

theorem block_eq (C : Context) (a : ℕ) : C.block a = cnt C.cuts (C.inst.pos a) := rfl

theorem cnt_split (l : List ℕ) (p q : ℕ) (h : p ≤ q) :
    cnt l q = cnt l p + (l.filter (fun s => decide (p ≤ s ∧ s < q))).length := by
  induction l with
  | nil => simp [cnt]
  | cons a l ih =>
    simp only [cnt, List.filter_cons] at ih ⊢
    split_ifs <;> simp only [List.length_cons, decide_eq_true_eq] at * <;> omega

theorem cnt_mono (l : List ℕ) (p q : ℕ) (h : p ≤ q) : cnt l p ≤ cnt l q := by
  have := cnt_split l p q h
  omega

theorem cnt_none (l : List ℕ) (p q : ℕ) (h : p ≤ q) (he : cnt l p = cnt l q) (s : ℕ)
    (hs : s ∈ l) (h1 : p ≤ s) (h2 : s < q) : False := by
  have hsp := cnt_split l p q h
  have hm : s ∈ l.filter (fun s => decide (p ≤ s ∧ s < q)) :=
    List.mem_filter.mpr ⟨hs, by simp [h1, h2]⟩
  have := List.length_pos_of_mem hm
  omega

theorem sym_mem (I : Instance) (u : Triple) (hu : u ∈ I.triples) :
    u.1 ∈ I.symbols ∧ u.2.1 ∈ I.symbols ∧ u.2.2 ∈ I.symbols := by
  unfold Instance.symbols
  refine ⟨List.mem_flatMap.mpr ⟨u, hu, ?_⟩, List.mem_flatMap.mpr ⟨u, hu, ?_⟩,
    List.mem_flatMap.mpr ⟨u, hu, ?_⟩⟩ <;> simp [Triple.symbols]

theorem disj_aux : ∀ (l : List Triple), (l.flatMap Triple.symbols).Nodup →
    ∀ u ∈ l, ∀ v ∈ l, ∀ e, e ∈ u.symbols → e ∈ v.symbols → u = v
  | [], _, u, hu, _, _, _, _, _ => by simp at hu
  | w :: l, hN, u, hu, v, hv, e, he1, he2 => by
    rw [List.flatMap_cons, List.nodup_append] at hN
    obtain ⟨_, hN2, hd⟩ := hN
    rcases List.mem_cons.mp hu with rfl | hu' <;> rcases List.mem_cons.mp hv with rfl | hv'
    · rfl
    · exact (hd e he1 e (List.mem_flatMap.mpr ⟨v, hv', he2⟩) rfl).elim
    · exact (hd e he2 e (List.mem_flatMap.mpr ⟨u, hu', he1⟩) rfl).elim
    · exact disj_aux l hN2 u hu' v hv' e he1 he2

theorem triples_nodup : ∀ (l : List Triple), (l.flatMap Triple.symbols).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | w :: l, hN => by
    rw [List.flatMap_cons, List.nodup_append] at hN
    obtain ⟨_, hN2, hd⟩ := hN
    refine List.nodup_cons.mpr ⟨fun hw => ?_, triples_nodup l hN2⟩
    exact hd w.1 (by simp [Triple.symbols]) w.1
      (List.mem_flatMap.mpr ⟨w, hw, by simp [Triple.symbols]⟩) rfl

theorem tc_cases (I : Instance) (t : Triple) :
    ((tripleCut I t).i = I.pos t.1 ∧ (tripleCut I t).j = I.pos t.2.1 ∧
      (tripleCut I t).k = I.pos t.2.2) ∨
    ((tripleCut I t).i = I.pos t.2.1 ∧ (tripleCut I t).j = I.pos t.2.2 ∧
      (tripleCut I t).k = I.pos t.1) ∨
    ((tripleCut I t).i = I.pos t.2.2 ∧ (tripleCut I t).j = I.pos t.1 ∧
      (tripleCut I t).k = I.pos t.2.1) := by
  simp only [tripleCut]
  split_ifs <;> simp

theorem blockD (C D : Context) (f : ℕ → ℕ) (hc : D.cuts = C.cuts.map f) (e Q : ℕ)
    (hpos : D.inst.pos e = f (C.inst.pos e))
    (h : ∀ s ∈ C.cuts, (f s < f (C.inst.pos e) ↔ s < Q)) :
    D.block e = cnt C.cuts Q := by
  unfold Context.block cnt
  rw [hc, hpos, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro s hs
  show decide (f s < f (C.inst.pos e)) = decide (s < Q)
  exact decide_eq_decide.mpr (h s hs)

theorem internal_transfer (C D : Context) (u : Triple)
    (hb : ∀ e, (e = u.1 ∨ e = u.2.1 ∨ e = u.2.2) → D.block e = C.block e) :
    Internal D u ↔ Internal C u := by
  unfold Internal
  rw [hb u.1 (by simp), hb u.2.1 (by simp), hb u.2.2 (by simp)]

theorem located_transfer (A : Variable) (C D : Context) (hL : A.Located C)
    (h1 : A.abc ∈ D.inst.triples) (h2 : A.xyz ∈ D.inst.triples)
    (hb : ∀ e, (e = A.abc.1 ∨ e = A.abc.2.1 ∨ e = A.abc.2.2 ∨ e = A.xyz.1 ∨
      e = A.xyz.2.1 ∨ e = A.xyz.2.2) → D.block e = C.block e) : A.Located D := by
  obtain ⟨_, _, hne, e1, e2, e3, e4, e5⟩ := hL
  have b1 := hb A.abc.1 (by simp)
  have b2 := hb A.abc.2.1 (by simp)
  have b3 := hb A.abc.2.2 (by simp)
  have b4 := hb A.xyz.1 (by simp)
  have b5 := hb A.xyz.2.1 (by simp)
  have b6 := hb A.xyz.2.2 (by simp)
  refine ⟨h1, h2, hne, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b2, b4]; exact e1
  · rw [b4, b5]; exact e2
  · rw [b1, b3]; exact e3
  · rw [b3, b6]; exact e4
  · rw [b2, b1]; exact e5

theorem remove_var (As : List Variable) (A : Variable) (hA : A ∈ As)
    (hN : (As.flatMap fun A => [A.abc, A.xyz]).Nodup) :
    ∃ As' : List Variable, (As'.flatMap fun A => [A.abc, A.xyz]).Nodup ∧
      (∀ B ∈ As', B ∈ As) ∧
      ∀ u, u ∈ As'.flatMap (fun A => [A.abc, A.xyz]) ↔
        (u ∈ As.flatMap (fun A => [A.abc, A.xyz]) ∧ u ≠ A.abc ∧ u ≠ A.xyz) := by
  obtain ⟨s, r, rfl⟩ := List.append_of_mem hA
  rw [List.flatMap_append, List.flatMap_cons] at hN
  obtain ⟨hP, hRQ, hd⟩ := List.nodup_append.mp hN
  obtain ⟨_, hQ, hd2⟩ := List.nodup_append.mp hRQ
  refine ⟨s ++ r, ?_, ?_, ?_⟩
  · rw [List.flatMap_append]
    exact List.nodup_append.mpr ⟨hP, hQ, fun a ha b hb => hd a ha b (List.mem_append_right _ hb)⟩
  · intro B hB
    rcases List.mem_append.mp hB with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · intro u
    rw [List.flatMap_append, List.flatMap_append, List.flatMap_cons]
    constructor
    · intro hu
      rcases List.mem_append.mp hu with hu | hu
      · exact ⟨List.mem_append_left _ hu, hd u hu _ (by simp), hd u hu _ (by simp)⟩
      · exact ⟨List.mem_append_right _ (List.mem_append_right _ hu),
          fun h => hd2 _ (by simp) u hu h.symm, fun h => hd2 _ (by simp) u hu h.symm⟩
    · rintro ⟨hu, h1, h2⟩
      rcases List.mem_append.mp hu with hu | hu
      · exact List.mem_append_left _ hu
      · rcases List.mem_append.mp hu with hu | hu
        · simp at hu
          tauto
        · exact List.mem_append_right _ hu

end Aux_BulteauTranspositions_NPHard_property_13

open BulteauTranspositions.NPHard Aux_BulteauTranspositions_NPHard_property_13 in
theorem solution (C D : Context) (t : Triple) (hv : ValidContext C)
    (hs : ContextStep C t D) :
    ∃ As, VariablePartition D As ∧ ∀ A ∈ As, A.Located D := by
  obtain ⟨_, _, hstep, hcuts⟩ := hs
  obtain ⟨hIwf, ⟨ht, hlegal⟩, _, htri, hposD⟩ := hstep
  obtain ⟨_, As, ⟨hN, hP⟩, hvalid⟩ := hv
  obtain ⟨_, hsymN, _, hinj⟩ := hIwf
  have hsymN' : (C.inst.triples.flatMap Triple.symbols).Nodup := hsymN
  obtain ⟨c, hc⟩ : ∃ c, c = tripleCut C.inst t := ⟨_, rfl⟩
  rw [← hc] at hcuts hposD hlegal
  have htc := tc_cases C.inst t
  rw [← hc] at htc
  obtain ⟨_, hij, hjk, _⟩ := hlegal
  have hTN := triples_nodup _ hsymN'
  have hDmem : ∀ u, u ∈ D.inst.triples ↔ u ≠ t ∧ u ∈ C.inst.triples := by
    intro u
    rw [htri]
    exact hTN.mem_erase_iff
  have hDsym : ∀ e ∈ D.inst.symbols, ∃ u ∈ C.inst.triples, u ≠ t ∧ e ∈ u.symbols := by
    intro e he
    obtain ⟨u, hu, heu⟩ :=
      List.mem_flatMap.mp (show e ∈ D.inst.triples.flatMap Triple.symbols from he)
    obtain ⟨hne, huC⟩ := (hDmem u).1 hu
    exact ⟨u, huC, hne, heu⟩
  have hCsym : ∀ e ∈ D.inst.symbols, e ∈ C.inst.symbols := by
    intro e he
    obtain ⟨u, huC, _, heu⟩ := hDsym e he
    show e ∈ C.inst.triples.flatMap Triple.symbols
    exact List.mem_flatMap.mpr ⟨u, huC, heu⟩
  have hblk : ∀ e ∈ D.inst.symbols, ∀ Q : ℕ,
      (∀ s ∈ C.cuts, (c.inv.tau s < c.inv.tau (C.inst.pos e) ↔ s < Q)) →
      D.block e = cnt C.cuts Q :=
    fun e he Q h => blockD C D c.inv.tau hcuts e Q (hposD e he) h
  by_cases hint : Internal C t
  · have hI' : cnt C.cuts (C.inst.pos t.1) = cnt C.cuts (C.inst.pos t.2.1) ∧
        cnt C.cuts (C.inst.pos t.2.1) = cnt C.cuts (C.inst.pos t.2.2) := hint
    have hik : cnt C.cuts c.i = cnt C.cuts c.k := by
      rcases htc with ⟨e1, _, e3⟩ | ⟨e1, _, e3⟩ | ⟨e1, _, e3⟩ <;> rw [e1, e3] <;> omega
    have hnone : ∀ s ∈ C.cuts, ¬ (c.i ≤ s ∧ s < c.k) :=
      fun s hs h => cnt_none C.cuts c.i c.k (by omega) hik s hs h.1 h.2
    have hb : ∀ e ∈ D.inst.symbols, D.block e = C.block e := by
      intro e he
      rw [block_eq C e]
      apply hblk e he
      intro s hs
      have hn := hnone s hs
      exact tau_iff c hij hjk s (C.inst.pos e) _ (by omega) (by omega) rfl
    have key : ∀ u ∈ D.inst.triples, (Internal D u ↔ Internal C u) := by
      intro u hu
      obtain ⟨s1, s2, s3⟩ := sym_mem D.inst u hu
      apply internal_transfer C D u
      intro e he
      rcases he with h | h | h <;> subst h
      · exact hb _ s1
      · exact hb _ s2
      · exact hb _ s3
    refine ⟨As, ⟨hN, fun u => ?_⟩, fun A hA => ?_⟩
    · constructor
      · rintro ⟨hu, hni⟩
        obtain ⟨_, huC⟩ := (hDmem u).1 hu
        exact (hP u).1 ⟨huC, fun hi => hni ((key u hu).2 hi)⟩
      · intro hu
        obtain ⟨huC, hni⟩ := (hP u).2 hu
        have hne : u ≠ t := fun h => hni (by rw [h]; exact hint)
        have huD := (hDmem u).2 ⟨hne, huC⟩
        exact ⟨huD, fun hi => hni ((key u huD).1 hi)⟩
    · have hL := (hvalid A hA).1
      have habcF : A.abc ∈ As.flatMap (fun A => [A.abc, A.xyz]) :=
        List.mem_flatMap.mpr ⟨A, hA, by simp⟩
      have hxyzF : A.xyz ∈ As.flatMap (fun A => [A.abc, A.xyz]) :=
        List.mem_flatMap.mpr ⟨A, hA, by simp⟩
      have habcD : A.abc ∈ D.inst.triples := by
        obtain ⟨huC, hni⟩ := (hP _).2 habcF
        exact (hDmem _).2 ⟨fun h => hni (by rw [h]; exact hint), huC⟩
      have hxyzD : A.xyz ∈ D.inst.triples := by
        obtain ⟨huC, hni⟩ := (hP _).2 hxyzF
        exact (hDmem _).2 ⟨fun h => hni (by rw [h]; exact hint), huC⟩
      obtain ⟨a1, a2, a3⟩ := sym_mem D.inst _ habcD
      obtain ⟨x1, x2, x3⟩ := sym_mem D.inst _ hxyzD
      apply located_transfer A C D hL habcD hxyzD
      intro e he
      rcases he with h | h | h | h | h | h <;> subst h
      · exact hb _ a1
      · exact hb _ a2
      · exact hb _ a3
      · exact hb _ x1
      · exact hb _ x2
      · exact hb _ x3
  · have htF : t ∈ As.flatMap (fun A => [A.abc, A.xyz]) := (hP t).1 ⟨ht, hint⟩
    obtain ⟨A, hA, htA⟩ := List.mem_flatMap.mp htF
    have htA' : t = A.abc ∨ t = A.xyz := by simpa using htA
    obtain ⟨hL, hcons, hbf1, hbf2⟩ := hvalid A hA
    have hL' := hL
    obtain ⟨habcC, hxyzC, hne, l1, l2, l3, l4, l5⟩ := hL'
    simp only [block_eq] at l1 l2 l3 l4 l5
    have hbf1' : C.inst.pos A.abc.1 < C.inst.pos A.xyz.2.2 := hbf1
    have hbf2' : C.inst.pos A.xyz.2.2 < C.inst.pos A.abc.2.2 := hbf2
    rcases htA' with rfl | rfl
    · exfalso
      rcases htc with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
      · have m1 := cnt_mono C.cuts _ _
          (show C.inst.pos A.abc.1 ≤ C.inst.pos A.abc.2.1 by omega)
        have m2 := cnt_mono C.cuts _ _
          (show C.inst.pos A.abc.2.1 ≤ C.inst.pos A.abc.2.2 by omega)
        omega
      · omega
      · omega
    · have hxy : C.inst.pos A.xyz.1 < C.inst.pos A.xyz.2.1 ∧
          ((c.i = C.inst.pos A.xyz.1 ∧ c.j = C.inst.pos A.xyz.2.1 ∧
              c.k = C.inst.pos A.xyz.2.2) ∨
            (c.i = C.inst.pos A.xyz.2.2 ∧ c.j = C.inst.pos A.xyz.1 ∧
              c.k = C.inst.pos A.xyz.2.1)) := by
        rcases htc with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
        · exact ⟨by omega, Or.inl ⟨e1, e2, e3⟩⟩
        · exfalso
          have m1 := cnt_mono C.cuts _ _
            (show C.inst.pos A.xyz.2.1 ≤ C.inst.pos A.xyz.2.2 by omega)
          have m2 := cnt_mono C.cuts _ _
            (show C.inst.pos A.xyz.2.2 ≤ C.inst.pos A.xyz.1 by omega)
          omega
        · exact ⟨by omega, Or.inr ⟨e1, e2, e3⟩⟩
      obtain ⟨hxy, hcase⟩ := hxy
      obtain ⟨⟨hxb, hcons1⟩, ⟨hby, hcons2⟩⟩ := hcons hxy
      have hxb' : C.inst.pos A.xyz.1 < C.inst.pos A.abc.2.1 := hxb
      have hby' : C.inst.pos A.abc.2.1 < C.inst.pos A.xyz.2.1 := hby
      have hnone : ∀ s ∈ C.cuts,
          ¬ (C.inst.pos A.xyz.1 ≤ s ∧ s < C.inst.pos A.xyz.2.1) :=
        fun s hs h => cnt_none C.cuts _ _ (le_of_lt hxy) l2 s hs h.1 h.2
      have hxD : A.xyz.1 ∉ D.inst.symbols := by
        intro hx
        obtain ⟨u, huC, hne', hxu⟩ := hDsym _ hx
        exact hne' (disj_aux _ hsymN' u huC A.xyz hxyzC _ hxu (by simp [Triple.symbols]))
      have hbC : A.abc.2.1 ∈ C.inst.symbols := (sym_mem _ _ habcC).2.1
      have hxC : A.xyz.1 ∈ C.inst.symbols := (sym_mem _ _ hxyzC).1
      have hnotin : ∀ e ∈ D.inst.symbols, e ≠ A.abc.2.1 →
          ¬ (C.inst.pos A.xyz.1 ≤ C.inst.pos e ∧ C.inst.pos e < C.inst.pos A.xyz.2.1) := by
        intro e he heb h
        obtain ⟨h1, h2⟩ := h
        have heC := hCsym e he
        rcases Nat.lt_trichotomy (C.inst.pos e) (C.inst.pos A.abc.2.1) with h3 | h3 | h3
        · rcases Nat.eq_or_lt_of_le h1 with h4 | h4
          · have hxe : A.xyz.1 = e := hinj hxC heC h4
            exact hxD (by rw [hxe]; exact he)
          · exact hcons1 ⟨e, heC, h4, h3⟩
        · exact heb (hinj heC hbC h3)
        · exact hcons2 ⟨e, heC, h3, h2⟩
      have hbe : ∀ e ∈ D.inst.symbols, e ≠ A.abc.2.1 → D.block e = C.block e := by
        intro e he heb
        have hn := hnotin e he heb
        rw [block_eq C e]
        apply hblk e he
        intro s hs
        have hs' := hnone s hs
        refine tau_iff c hij hjk s _ _ ?_ ?_ rfl
        · rcases hcase with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> omega
        · rcases hcase with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> omega
      have habcD : A.abc ∈ D.inst.triples := (hDmem _).2 ⟨hne, habcC⟩
      obtain ⟨sa, sb, sc⟩ := sym_mem _ _ habcD
      have hbD : D.block A.abc.2.1 = cnt C.cuts (C.inst.pos A.xyz.2.2) := by
        apply hblk _ sb
        intro s hs
        exact tau_iff_b c hij hjk s _ _ _ _ hcase hxb' hby' (hnone s hs)
      have hab : A.abc.1 ≠ A.abc.2.1 := fun h => l5 (by rw [h])
      have hcb : A.abc.2.2 ≠ A.abc.2.1 := fun h => l5 (by rw [← h]; omega)
      have hintD : Internal D A.abc := by
        unfold Internal
        rw [hbe _ sa hab, hbD, hbe _ sc hcb, block_eq, block_eq]
        refine ⟨?_, ?_⟩ <;> omega
      have hbu : ∀ u ∈ D.inst.triples, u ≠ A.abc →
          ∀ e, (e = u.1 ∨ e = u.2.1 ∨ e = u.2.2) → D.block e = C.block e := by
        intro u hu hua e he
        have hs3 := sym_mem _ _ hu
        have heD : e ∈ D.inst.symbols ∧ e ∈ u.symbols := by
          rcases he with rfl | rfl | rfl
          · exact ⟨hs3.1, by simp [Triple.symbols]⟩
          · exact ⟨hs3.2.1, by simp [Triple.symbols]⟩
          · exact ⟨hs3.2.2, by simp [Triple.symbols]⟩
        apply hbe e heD.1
        intro heb
        obtain ⟨_, huC⟩ := (hDmem u).1 hu
        exact hua (disj_aux _ hsymN' u huC A.abc habcC e heD.2
          (by rw [heb]; simp [Triple.symbols]))
      obtain ⟨As', hN', hsub, hmem⟩ := remove_var As A hA hN
      refine ⟨As', ⟨hN', fun u => ?_⟩, fun B hB => ?_⟩
      · constructor
        · rintro ⟨hu, hni⟩
          obtain ⟨hut, huC⟩ := (hDmem u).1 hu
          have hua : u ≠ A.abc := fun h => hni (by rw [h]; exact hintD)
          exact (hmem u).2 ⟨(hP u).1 ⟨huC, fun hi =>
            hni ((internal_transfer C D u (hbu u hu hua)).2 hi)⟩, hua, hut⟩
        · intro hu
          obtain ⟨huF, hua, hux⟩ := (hmem u).1 hu
          obtain ⟨huC, hni⟩ := (hP u).2 huF
          have huD := (hDmem u).2 ⟨hux, huC⟩
          exact ⟨huD, fun hi => hni ((internal_transfer C D u (hbu u huD hua)).1 hi)⟩
      · have hBA := hsub B hB
        have hLB := (hvalid B hBA).1
        have h1 : B.abc ∈ As'.flatMap (fun A => [A.abc, A.xyz]) :=
          List.mem_flatMap.mpr ⟨B, hB, by simp⟩
        have h2 : B.xyz ∈ As'.flatMap (fun A => [A.abc, A.xyz]) :=
          List.mem_flatMap.mpr ⟨B, hB, by simp⟩
        obtain ⟨h1F, h1a, h1x⟩ := (hmem _).1 h1
        obtain ⟨h2F, h2a, h2x⟩ := (hmem _).1 h2
        have h1D := (hDmem _).2 ⟨h1x, ((hP _).2 h1F).1⟩
        have h2D := (hDmem _).2 ⟨h2x, ((hP _).2 h2F).1⟩
        apply located_transfer B C D hLB h1D h2D
        intro e he
        rcases he with h | h | h | h | h | h
        · exact hbu _ h1D h1a e (Or.inl h)
        · exact hbu _ h1D h1a e (Or.inr (Or.inl h))
        · exact hbu _ h1D h1a e (Or.inr (Or.inr h))
        · exact hbu _ h2D h2a e (Or.inl h)
        · exact hbu _ h2D h2a e (Or.inr (Or.inl h))
        · exact hbu _ h2D h2a e (Or.inr (Or.inr h))
