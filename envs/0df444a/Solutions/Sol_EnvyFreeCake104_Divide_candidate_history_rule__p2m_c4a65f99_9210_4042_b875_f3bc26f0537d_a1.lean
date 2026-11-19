-- Prove2me | solution 1 for EnvyFreeCake104.Divide.candidate_history_rule__p2m_c4a65f99_9210_4042_b875_f3bc26f0537d_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-18T18:56:54.327277+00:00
-- url     : https://prove2.me/submissions/d5100522-de40-414f-93df-b02f11cecd62

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

open EnvyFreeCake104.Divide

set_option autoImplicit false

private theorem run_bind__p2m_8a7f91d3_630e_4699_950d_8a04643e5004_a2
    {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (m : Prog ι α) (f : α → Prog ι β) (tr : List (Event ι)) :
    Prog.run V o (Prog.bind m f) tr =
      match Prog.run V o m tr with
      | none => none
      | some (x, tr') => Prog.run V o (f x) tr' := by
  induction m generalizing tr with
  | ret x => rfl
  | fail => rfl
  | eval i a b k ih =>
      simpa only [Prog.bind, Prog.run] using ih (evalAnswer V i a b) _
  | cut i x w k ih =>
      simpa only [Prog.bind, Prog.run] using ih (cutAnswer V i x w) _
  | choose n k ih =>
      simpa only [Prog.bind, Prog.run] using ih (o tr n) _

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (K : List ι → (ι → Piece) → Piece → Piece → Prop)
    (hstable : ∀ (earlier : List ι) (Y Z : ι → Piece) (Q B : Piece),
      (∀ i ∈ earlier, Y i = Z i) → K earlier Y Q B → K earlier Z Q B)
    (htrim : ∀ (Y : ι → Piece) (earlier : List ι) (Q : Piece) (s : Rec ι),
      (∀ i ∈ N, (Y i).WF) → (∀ i ∈ earlier, i ∈ N) →
      Q.WF → s.Valid V N →
      (∀ i ∈ N, s.Aligned (Y i)) → s.Aligned Q →
      ∀ (o : ChoiceOracle ι) (tr₀ : List (Event ι)),
      ∃ (B rem : Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((trimAgainst N Y earlier Q []).run s) tr₀ =
          some (((B, rem), s'), tr) ∧
        s'.Valid V N ∧ s.pts ⊆ s'.pts ∧ B.WF ∧ s'.Aligned B ∧ K earlier Y Q B)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (ag pc : List ι) (hag : ag.Nodup)
    (hmem : ∀ p ∈ ag.zip pc, p.1 ∈ N ∧ p.2 ∈ N) (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (candidate N P ag pc) s = some ((Y, R), s', tr) ∧
      ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
        ag.zip pc = before ++ p :: after →
        K (before.map Prod.fst) Y (P p.2) (Y p.1) := by
  classical
  have loop : ∀ (todo : List (ι × ι)), (todo.map Prod.fst).Nodup →
      (∀ p ∈ todo, p.1 ∈ N ∧ p.2 ∈ N) →
      ∀ (earlier : List ι) (Y : ι → Piece) (R : Piece) (st : Rec ι)
        (tr₀ : List (Event ι)),
      (∀ i ∈ earlier, i ∈ N) →
      (∀ i ∈ earlier, i ∉ todo.map Prod.fst) →
      (∀ i ∈ N, (Y i).WF) → st.Valid V N →
      (∀ i ∈ N, st.Aligned (Y i)) → (∀ i ∈ N, st.Aligned (P i)) →
      ∃ (Z : ι → Piece) (R' : Piece) (st' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((candidateLoop N P todo earlier Y R).run st) tr₀ =
          some (((Z, R'), st'), tr) ∧
        (∀ i, i ∉ todo.map Prod.fst → Z i = Y i) ∧
        ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
          todo = before ++ p :: after →
          K (earlier ++ before.map Prod.fst) Z (P p.2) (Z p.1) := by
    intro todo
    induction todo with
    | nil =>
        intro hn hm earlier Y R st tr₀ he hd hw hv ha hp
        refine ⟨Y, R, st, tr₀, rfl, ?_, ?_⟩
        · intro i hi
          rfl
        · intro before p after hh
          have hl := congrArg List.length hh
          simp at hl
    | cons pair rest ih =>
        rcases pair with ⟨i, j⟩
        intro hn hm earlier Y R st tr₀ he hd hw hv ha hp
        have hn' : i ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
          simpa only [List.map_cons, List.nodup_cons] using hn
        have hij := hm (i, j) (by simp)
        obtain ⟨B, rem, st₁, tr₁, ht, hv₁, hpts, hB, haB, hK⟩ :=
          htrim Y earlier (P j) st hw he (hP j hij.2) hv ha (hp j hij.2) o tr₀
        have he' : ∀ k ∈ earlier ++ [i], k ∈ N := by
          intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact he k hk
          · simpa only [List.mem_singleton.mp hk] using hij.1
        have hd' : ∀ k ∈ earlier ++ [i], k ∉ rest.map Prod.fst := by
          intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact fun h => hd k hk (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h)
          · simpa only [List.mem_singleton.mp hk] using hn'.1
        have hw' : ∀ k ∈ N, (Function.update Y i B k).WF := by
          intro k hk
          by_cases hki : k = i
          · subst k
            simpa using hB
          · simpa [Function.update, hki] using hw k hk
        have ha' : ∀ k ∈ N, st₁.Aligned (Function.update Y i B k) := by
          intro k hk
          by_cases hki : k = i
          · subst k
            simpa using haB
          · rw [Function.update_of_ne hki]
            intro I hI
            exact ⟨hpts (ha k hk I hI).1, hpts (ha k hk I hI).2⟩
        have hp' : ∀ k ∈ N, st₁.Aligned (P k) := by
          intro k hk I hI
          exact ⟨hpts (hp k hk I hI).1, hpts (hp k hk I hI).2⟩
        obtain ⟨Z, R', st', tr, hr, hz, hhist⟩ :=
          ih hn'.2 (fun p h => hm p (by simp only [List.mem_cons]; exact Or.inr h))
            (earlier ++ [i]) (Function.update Y i B) (R ++ rem) st₁ tr₁
            he' hd' hw' hv₁ ha' hp'
        have hzi : Z i = B := by simpa using hz i hn'.1
        refine ⟨Z, R', st', tr, ?_, ?_, ?_⟩
        · change Prog.run V o
            (Prog.bind ((trimAgainst N Y earlier (P j) []).run st)
              (fun x => (candidateLoop N P rest (earlier ++ [i])
                (Function.update Y i x.1.1) (R ++ x.1.2)).run x.2)) tr₀ = _
          rw [run_bind__p2m_8a7f91d3_630e_4699_950d_8a04643e5004_a2, ht]
          exact hr
        · intro k hk
          have hk' : k ≠ i ∧ k ∉ rest.map Prod.fst := by
            simpa only [List.map_cons, List.mem_cons, not_or] using hk
          rw [hz k hk'.2, Function.update_of_ne hk'.1]
        · intro before p after hh
          cases before with
          | nil =>
              have hhead : (i, j) = p := (List.cons.inj hh).1
              subst p
              simp only [List.map_nil, List.append_nil]
              rw [hzi]
              apply hstable earlier Y Z (P j) B ?_ hK
              intro k hk
              have hki : k ≠ i := by
                intro h
                exact hd k hk (by simp [h])
              exact (by rw [hz k (hd' k (List.mem_append.mpr (Or.inl hk))),
                Function.update_of_ne hki])
          | cons b bs =>
              obtain ⟨hhead, htail⟩ : (i, j) = b ∧ rest = bs ++ p :: after :=
                List.cons.inj hh
              subst b
              simpa only [List.map_cons, List.append_assoc, List.singleton_append] using
                hhist bs p after htail
  have zip_nodup : ∀ (aa bb : List ι), aa.Nodup →
      ((aa.zip bb).map Prod.fst).Nodup := by
    intro aa
    induction aa with
    | nil => simp
    | cons a as ih =>
        intro bb hn
        cases bb with
        | nil => simp
        | cons b bs =>
            have ha := List.nodup_cons.mp hn
            simp only [List.zip_cons_cons, List.map_cons, List.nodup_cons]
            refine ⟨?_, ih bs ha.2⟩
            intro h
            obtain ⟨p, hp, heq⟩ := List.mem_map.mp h
            have hpa := (List.of_mem_zip hp).1
            exact ha.1 (by simpa only [heq] using hpa)
  obtain ⟨Y, R, s', tr, hr, hu, hh⟩ :=
    loop (ag.zip pc) (zip_nodup ag pc hag) hmem [] (fun _ => []) [] s []
      (by simp) (by simp) (by intro i hi; exact ⟨by simp, by simp⟩)
      hs (by intro i hi; intro I hI; simp at hI) hPs
  refine ⟨Y, R, s', tr, ?_, ?_⟩
  · unfold exec candidate
    rw [hr]
  · simpa only [List.nil_append] using hh
