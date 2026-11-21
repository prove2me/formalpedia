-- Prove2me | solution 1 for BulteauTranspositions.NPHard.property_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:00:44.942061+00:00
-- url     : https://prove2.me/submissions/0b9fd331-40c5-4133-a36c-d90cf4b670d5

import Definitions.Def_BulteauTranspositions_NPHard_Blocks

namespace Aux_BulteauTranspositions_NPHard_property_16

open BulteauTranspositions.NPHard

/-! ### Renaming of symbols -/

def mapT (φ : ℕ → ℕ) (t : Triple) : Triple := (φ t.1, φ t.2.1, φ t.2.2)
def mapV (φ : ℕ → ℕ) (A : Variable) : Variable := ⟨mapT φ A.abc, mapT φ A.xyz⟩
def mapS (φ : ℕ → ℕ) (S : LocalState) : LocalState :=
  ⟨S.word.map φ, S.internalTriples.map (mapT φ), S.inputs.map (mapV φ),
    S.outputs.map (mapV φ)⟩

def TOk (P : ℕ → Prop) (t : Triple) : Prop := P t.1 ∧ P t.2.1 ∧ P t.2.2
def VOk (P : ℕ → Prop) (A : Variable) : Prop := TOk P A.abc ∧ TOk P A.xyz
def SOk (P : ℕ → Prop) (S : LocalState) : Prop :=
  (∀ x ∈ S.word, P x) ∧ (∀ t ∈ S.internalTriples, TOk P t) ∧
  (∀ A ∈ S.inputs, VOk P A) ∧ (∀ A ∈ S.outputs, VOk P A)
def InjP (P : ℕ → Prop) (φ : ℕ → ℕ) : Prop := ∀ x y, P x → P y → φ x = φ y → x = y

theorem mapT_inj {P : ℕ → Prop} {φ : ℕ → ℕ} (hφ : InjP P φ) {t t' : Triple}
    (ht : TOk P t) (ht' : TOk P t') (h : mapT φ t = mapT φ t') : t = t' := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨a', b', c'⟩ := t'
  simp only [mapT, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨p1, p2, p3⟩ := ht
  obtain ⟨q1, q2, q3⟩ := ht'
  have e1 : a = a' := hφ a a' p1 q1 h1
  have e2 : b = b' := hφ b b' p2 q2 h2
  have e3 : c = c' := hφ c c' p3 q3 h3
  rw [e1, e2, e3]

theorem mapV_inj {P : ℕ → Prop} {φ : ℕ → ℕ} (hφ : InjP P φ) {A B : Variable}
    (hA : VOk P A) (hB : VOk P B) (h : mapV φ A = mapV φ B) : A = B := by
  obtain ⟨a1, a2⟩ := A
  obtain ⟨b1, b2⟩ := B
  simp only [mapV, Variable.mk.injEq] at h
  have e1 : a1 = b1 := mapT_inj hφ hA.1 hB.1 h.1
  have e2 : a2 = b2 := mapT_inj hφ hA.2 hB.2 h.2
  rw [e1, e2]

theorem map_erase_on {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (a : α) :
    ∀ (l : List α), (∀ x ∈ l, f x = f a → x = a) → (l.erase a).map f = (l.map f).erase (f a)
  | [], _ => by simp
  | b :: l, h => by
    by_cases hb : b = a
    · subst hb
      simp
    · have hfb : f b ≠ f a := fun e => hb (h b List.mem_cons_self e)
      rw [List.erase_cons_tail (by simpa using hb), List.map_cons, List.map_cons,
        List.erase_cons_tail (by simpa using hfb),
        map_erase_on f a l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem cyc_map (φ : ℕ → ℕ) {t u : Triple} (h : Cyclic t u) : Cyclic (mapT φ t) (mapT φ u) := by
  rcases h with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem cyc_ok {P : ℕ → Prop} {t u : Triple} (h : Cyclic t u) (ht : TOk P t) : TOk P u := by
  rcases h with rfl | rfl | rfl
  · exact ht
  · exact ⟨ht.2.1, ht.2.2, ht.1⟩
  · exact ⟨ht.2.2, ht.1, ht.2.1⟩

theorem toList_mapV (φ : ℕ → ℕ) (o : Option Variable) :
    o.toList.map (mapV φ) = (o.map (mapV φ)).toList := by
  cases o <;> rfl

theorem arc_ok {P : ℕ → Prop} {S T : LocalState} {e : Option Variable}
    (h : LocalArc S e T) (hS : SOk P S) : SOk P T := by
  obtain ⟨hwd, hi, hin, hout⟩ := hS
  cases h with
  | internal t u R X Y Z ht hc hw =>
    refine ⟨?_, ?_, hin, hout⟩
    · intro x hx
      apply hwd x
      rw [hw]
      simp only [List.mem_append, List.mem_singleton] at hx ⊢
      tauto
    · intro t' ht'
      exact hi t' (List.mem_of_mem_erase ht')
  | input A R U V W ha hw =>
    have hA := hin A ha
    refine ⟨?_, ?_, ?_, hout⟩
    · intro x hx
      by_cases hx2 : x = A.abc.2.1
      · rw [hx2]
        exact hA.1.2.1
      · apply hwd x
        rw [hw]
        simp only [List.mem_append, List.mem_singleton] at hx ⊢
        tauto
    · intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact hA.1
      · exact hi t' ht'
    · intro B hB
      exact hin B (List.mem_of_mem_erase hB)
  | output A R Tl ha hw =>
    refine ⟨?_, hi, hin, ?_⟩
    · intro x hx
      apply hwd x
      rw [hw]
      simp only [List.mem_append] at hx ⊢
      tauto
    · intro B hB
      exact hout B (List.mem_of_mem_erase hB)

theorem arc_map {P : ℕ → Prop} {φ : ℕ → ℕ} (hφ : InjP P φ) {S T : LocalState}
    {e : Option Variable} (h : LocalArc S e T) (hS : SOk P S) :
    LocalArc (mapS φ S) (e.map (mapV φ)) (mapS φ T) := by
  obtain ⟨hwd, hi, hin, hout⟩ := hS
  cases h with
  | internal t u R X Y Z ht hc hw =>
    have hT := LocalArc.internal (mapS φ S) (mapT φ t) (mapT φ u) (R.map φ) (X.map φ)
      (Y.map φ) (Z.map φ) (List.mem_map_of_mem ht) (cyc_map φ hc)
      (by show S.word.map φ = _; rw [hw]; simp [mapT])
    convert hT using 1
    all_goals first
      | rfl
      | simp only [mapS, List.map_append, map_erase_on (mapT φ) t S.internalTriples
          (fun x hx hxt => mapT_inj hφ (hi x hx) (hi t ht) hxt)]
  | input A R U V W ha hw =>
    have hA := hin A ha
    have hT := LocalArc.input (mapS φ S) (mapV φ A) (R.map φ) (U.map φ) (V.map φ) (W.map φ)
      (List.mem_map_of_mem ha) (by show S.word.map φ = _; rw [hw]; simp [mapV, mapT])
    convert hT using 1
    all_goals first
      | rfl
      | simp only [mapS, List.map_append, List.map_cons, List.map_nil, mapV, mapT,
          map_erase_on (mapV φ) A S.inputs (fun x hx hxA => mapV_inj hφ (hin x hx) hA hxA)]
  | output A R Tl ha hw =>
    have hA := hout A ha
    have hT := LocalArc.output (mapS φ S) (mapV φ A) (R.map φ) (Tl.map φ)
      (List.mem_map_of_mem ha) (by show S.word.map φ = _; rw [hw]; simp [mapV, mapT])
    convert hT using 1
    all_goals first
      | rfl
      | simp only [mapS, List.map_append,
          map_erase_on (mapV φ) A S.outputs (fun x hx hxA => mapV_inj hφ (hout x hx) hA hxA)]

theorem pull3 {φ : ℕ → ℕ} {L R' X' Y' Z' : List ℕ} {a' b' c' : ℕ}
    (h : L.map φ = R' ++ [a'] ++ X' ++ [b'] ++ Y' ++ [c'] ++ Z') :
    ∃ R a X b Y c Z, L = R ++ [a] ++ X ++ [b] ++ Y ++ [c] ++ Z ∧ R.map φ = R' ∧ φ a = a' ∧
      X.map φ = X' ∧ φ b = b' ∧ Y.map φ = Y' ∧ φ c = c' ∧ Z.map φ = Z' := by
  simp only [List.append_assoc, List.singleton_append] at h
  obtain ⟨R, L1, rfl, hR, h1⟩ := List.map_eq_append_iff.mp h
  obtain ⟨a, L2, rfl, ha, h2⟩ := List.map_eq_cons_iff.mp h1
  obtain ⟨X, L3, rfl, hX, h3⟩ := List.map_eq_append_iff.mp h2
  obtain ⟨b, L4, rfl, hb, h4⟩ := List.map_eq_cons_iff.mp h3
  obtain ⟨Y, L5, rfl, hY, h5⟩ := List.map_eq_append_iff.mp h4
  obtain ⟨c, Z, rfl, hc, hZ⟩ := List.map_eq_cons_iff.mp h5
  exact ⟨R, a, X, b, Y, c, Z, by simp, hR, ha, hX, hb, hY, hc, hZ⟩

theorem pullO {φ : ℕ → ℕ} {L R' T' : List ℕ} {p q r : ℕ}
    (h : L.map φ = R' ++ [p, q, r] ++ T') :
    ∃ R a b c T, L = R ++ [a, b, c] ++ T ∧ R.map φ = R' ∧ φ a = p ∧ φ b = q ∧ φ c = r ∧
      T.map φ = T' := by
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  obtain ⟨R, L1, rfl, hR, h1⟩ := List.map_eq_append_iff.mp h
  obtain ⟨a, L2, rfl, ha, h2⟩ := List.map_eq_cons_iff.mp h1
  obtain ⟨b, L3, rfl, hb, h3⟩ := List.map_eq_cons_iff.mp h2
  obtain ⟨c, T, rfl, hc, hT⟩ := List.map_eq_cons_iff.mp h3
  exact ⟨R, a, b, c, T, by simp, hR, ha, hb, hc, hT⟩

theorem arc_pull {P : ℕ → Prop} {φ : ℕ → ℕ} (hφ : InjP P φ) {S : LocalState} (hS : SOk P S)
    {S' : LocalState} {e' : Option Variable} {T' : LocalState} (h : LocalArc S' e' T')
    (hSS : mapS φ S = S') :
    ∃ e T, LocalArc S e T ∧ e' = e.map (mapV φ) ∧ T' = mapS φ T := by
  obtain ⟨hwd, hi, hin, hout⟩ := hS
  cases h with
  | internal t' u' R' X' Y' Z' ht hc hw =>
    subst hSS
    have ht2 : t' ∈ S.internalTriples.map (mapT φ) := ht
    obtain ⟨t, ht0, rfl⟩ := List.mem_map.mp ht2
    have hu : ∃ u, Cyclic t u ∧ u' = mapT φ u := by
      rcases hc with rfl | rfl | rfl
      · exact ⟨t, Or.inl rfl, rfl⟩
      · exact ⟨(t.2.1, t.2.2, t.1), Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨(t.2.2, t.1, t.2.1), Or.inr (Or.inr rfl), rfl⟩
    obtain ⟨u, hcu, rfl⟩ := hu
    have hTu : TOk P u := cyc_ok hcu (hi t ht0)
    obtain ⟨R, a, X, b, Y, c, Z, hL, rfl, ha, rfl, hb, rfl, hc', rfl⟩ :=
      pull3 (show S.word.map φ = _ from hw)
    have hPa : P a := hwd a (by rw [hL]; simp)
    have hPb : P b := hwd b (by rw [hL]; simp)
    have hPc : P c := hwd c (by rw [hL]; simp)
    have ea : a = u.1 := hφ _ _ hPa hTu.1 ha
    have eb : b = u.2.1 := hφ _ _ hPb hTu.2.1 hb
    have ec : c = u.2.2 := hφ _ _ hPc hTu.2.2 hc'
    subst ea eb ec
    refine ⟨none, { S with
        word := R ++ Y ++ X ++ Z
        internalTriples := S.internalTriples.erase t },
      LocalArc.internal S t u R X Y Z ht0 hcu hL, rfl, ?_⟩
    simp only [mapS, List.map_append, map_erase_on (mapT φ) t S.internalTriples
      (fun x hx hxt => mapT_inj hφ (hi x hx) (hi t ht0) hxt)]
  | input A' R' U' V' W' ha hw =>
    subst hSS
    have ha2 : A' ∈ S.inputs.map (mapV φ) := ha
    obtain ⟨A, hA0, rfl⟩ := List.mem_map.mp ha2
    have hA := hin A hA0
    obtain ⟨R, a, U, b, V, c, W, hL, rfl, ha', rfl, hb, rfl, hc', rfl⟩ :=
      pull3 (show S.word.map φ = _ from hw)
    have hPa : P a := hwd a (by rw [hL]; simp)
    have hPb : P b := hwd b (by rw [hL]; simp)
    have hPc : P c := hwd c (by rw [hL]; simp)
    have ea : a = A.abc.1 := hφ _ _ hPa hA.1.1 ha'
    have eb : b = A.xyz.2.2 := hφ _ _ hPb hA.2.2.2 hb
    have ec : c = A.abc.2.2 := hφ _ _ hPc hA.1.2.2 hc'
    subst ea eb ec
    refine ⟨some A, { S with
      word := R ++ [A.abc.1] ++ U ++ [A.abc.2.1] ++ V ++ [A.abc.2.2] ++ W,
      inputs := S.inputs.erase A, internalTriples := A.abc :: S.internalTriples },
      LocalArc.input S A R U V W hA0 hL, rfl, ?_⟩
    simp only [mapS, List.map_append, List.map_cons, List.map_nil, mapV, mapT,
      map_erase_on (mapV φ) A S.inputs (fun x hx hxA => mapV_inj hφ (hin x hx) hA hxA)]
  | output A' R' T0 ha hw =>
    subst hSS
    have ha2 : A' ∈ S.outputs.map (mapV φ) := ha
    obtain ⟨A, hA0, rfl⟩ := List.mem_map.mp ha2
    have hA := hout A hA0
    obtain ⟨R, a, b, c, Tl, hL, rfl, ha', hb, hc', rfl⟩ :=
      pullO (show S.word.map φ = _ from hw)
    have hPa : P a := hwd a (by rw [hL]; simp)
    have hPb : P b := hwd b (by rw [hL]; simp)
    have hPc : P c := hwd c (by rw [hL]; simp)
    have ea : a = A.xyz.1 := hφ _ _ hPa hA.2.1 ha'
    have eb : b = A.abc.2.1 := hφ _ _ hPb hA.1.2.1 hb
    have ec : c = A.xyz.2.1 := hφ _ _ hPc hA.2.2.1 hc'
    subst ea eb ec
    refine ⟨some A, { S with word := R ++ Tl, outputs := S.outputs.erase A },
      LocalArc.output S A R Tl hA0 hL, rfl, ?_⟩
    simp only [mapS, List.map_append,
      map_erase_on (mapV φ) A S.outputs (fun x hx hxA => mapV_inj hφ (hout x hx) hA hxA)]

theorem run_ok {P : ℕ → Prop} {S U : LocalState} {es : List Variable}
    (h : LocalRun S es U) : SOk P S → SOk P U := by
  induction h with
  | refl _ => exact id
  | step harc _ ih => exact fun hS => ih (arc_ok harc hS)

theorem run_map {P : ℕ → Prop} {φ : ℕ → ℕ} (hφ : InjP P φ) {S U : LocalState}
    {es : List Variable} (h : LocalRun S es U) :
    SOk P S → LocalRun (mapS φ S) (es.map (mapV φ)) (mapS φ U) := by
  induction h with
  | refl S0 => exact fun _ => LocalRun.refl _
  | @step S0 T0 U0 e0 es0 harc _ ih =>
    intro hS
    have hr := LocalRun.step (arc_map hφ harc hS) (ih (arc_ok harc hS))
    rw [List.map_append, toList_mapV]
    exact hr

theorem run_pull {P : ℕ → Prop} {φ : ℕ → ℕ} (hφ : InjP P φ) {S' U' : LocalState}
    {es' : List Variable} (h : LocalRun S' es' U') :
    ∀ S, SOk P S → mapS φ S = S' →
      ∃ es U, LocalRun S es U ∧ es' = es.map (mapV φ) ∧ U' = mapS φ U := by
  induction h with
  | refl S0 =>
    intro S _ hS
    exact ⟨[], S, LocalRun.refl S, rfl, hS.symm⟩
  | @step S0 T0 U0 e0 es0 harc _ ih =>
    intro S hok hS
    obtain ⟨e, T, harcT, rfl, rfl⟩ := arc_pull hφ hok harc hS
    obtain ⟨es, U, hrun, rfl, rfl⟩ := ih T (arc_ok harcT hok) rfl
    refine ⟨e.toList ++ es, U, LocalRun.step harcT hrun, ?_, rfl⟩
    rw [List.map_append, toList_mapV]

/-! ### A decision procedure for local runs -/

def splits : List ℕ → List (List ℕ × ℕ × List ℕ)
  | [] => []
  | x :: xs => ([], x, xs) :: (splits xs).map (fun p => (x :: p.1, p.2.1, p.2.2))

theorem mem_splits_of (L : List ℕ) :
    ∀ (R T : List ℕ) (a : ℕ), (R, a, T) ∈ splits L → L = R ++ a :: T := by
  induction L with
  | nil => intro R T a h; simp [splits] at h
  | cons x xs ih =>
    intro R T a h
    simp only [splits, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨⟨R', a', T'⟩, hp, he⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      simp [ih R' T' a' hp]

theorem mem_splits_of_eq (L R T : List ℕ) (a : ℕ) (h : L = R ++ a :: T) :
    (R, a, T) ∈ splits L := by
  subst h
  induction R with
  | nil => simp [splits]
  | cons r R ih =>
    show (r :: R, a, T) ∈ splits (r :: (R ++ a :: T))
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(R, a, T), ih, rfl⟩)

def rots (t : Triple) : List Triple := [t, (t.2.1, t.2.2, t.1), (t.2.2, t.1, t.2.1)]

theorem rots_cyc {t u : Triple} (h : u ∈ rots t) : Cyclic t u := by
  unfold Cyclic
  simpa [rots] using h

theorem cyc_rots {t u : Triple} (h : Cyclic t u) : u ∈ rots t := by
  rcases h with rfl | rfl | rfl <;> simp [rots]

def succI (S : LocalState) : List (Option Variable × LocalState) :=
  S.internalTriples.flatMap fun t => (rots t).flatMap fun u =>
    ((splits S.word).filter (fun p => p.2.1 = u.1)).flatMap fun p1 =>
    ((splits p1.2.2).filter (fun p => p.2.1 = u.2.1)).flatMap fun p2 =>
    ((splits p2.2.2).filter (fun p => p.2.1 = u.2.2)).map fun p3 =>
      ((none : Option Variable), { S with
        word := p1.1 ++ p3.1 ++ p2.1 ++ p3.2.2
        internalTriples := S.internalTriples.erase t })

def succIn (S : LocalState) : List (Option Variable × LocalState) :=
  S.inputs.flatMap fun A =>
    ((splits S.word).filter (fun p => p.2.1 = A.abc.1)).flatMap fun p1 =>
    ((splits p1.2.2).filter (fun p => p.2.1 = A.xyz.2.2)).flatMap fun p2 =>
    ((splits p2.2.2).filter (fun p => p.2.1 = A.abc.2.2)).map fun p3 =>
      (some A, { S with
        word := p1.1 ++ [A.abc.1] ++ p2.1 ++ [A.abc.2.1] ++ p3.1 ++ [A.abc.2.2] ++ p3.2.2,
        inputs := S.inputs.erase A, internalTriples := A.abc :: S.internalTriples })

def succOut (S : LocalState) : List (Option Variable × LocalState) :=
  S.outputs.flatMap fun A =>
    ((splits S.word).filter
      (fun p => p.2.1 = A.xyz.1 ∧ p.2.2.take 2 = [A.abc.2.1, A.xyz.2.1])).map fun p1 =>
      (some A, { S with word := p1.1 ++ p1.2.2.drop 2, outputs := S.outputs.erase A })

def succ (S : LocalState) : List (Option Variable × LocalState) :=
  succI S ++ succIn S ++ succOut S

theorem succ_sound {S T : LocalState} {e : Option Variable} (h : (e, T) ∈ succ S) :
    LocalArc S e T := by
  simp only [succ, List.mem_append] at h
  rcases h with (h | h) | h
  · simp only [succI, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
    obtain ⟨t, ht, u, hu, ⟨R, a, L1⟩, ⟨hp1, ha⟩, ⟨X, b, L2⟩, ⟨hp2, hb⟩, ⟨Y, c, Z⟩,
      ⟨hp3, hc⟩, he⟩ := h
    have e1 : S.word = R ++ a :: L1 := mem_splits_of _ _ _ _ hp1
    have e2 : L1 = X ++ b :: L2 := mem_splits_of _ _ _ _ hp2
    have e3 : L2 = Y ++ c :: Z := mem_splits_of _ _ _ _ hp3
    have ha' : a = u.1 := ha
    have hb' : b = u.2.1 := hb
    have hc' : c = u.2.2 := hc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact LocalArc.internal S t u R X Y Z ht (rots_cyc hu)
      (by rw [e1, e2, e3, ha', hb', hc']; simp)
  · simp only [succIn, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
    obtain ⟨A, hA, ⟨R, a, L1⟩, ⟨hp1, ha⟩, ⟨X, b, L2⟩, ⟨hp2, hb⟩, ⟨Y, c, Z⟩,
      ⟨hp3, hc⟩, he⟩ := h
    have e1 : S.word = R ++ a :: L1 := mem_splits_of _ _ _ _ hp1
    have e2 : L1 = X ++ b :: L2 := mem_splits_of _ _ _ _ hp2
    have e3 : L2 = Y ++ c :: Z := mem_splits_of _ _ _ _ hp3
    have ha' : a = A.abc.1 := ha
    have hb' : b = A.xyz.2.2 := hb
    have hc' : c = A.abc.2.2 := hc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact LocalArc.input S A R X Y Z hA (by rw [e1, e2, e3, ha', hb', hc']; simp)
  · simp only [succOut, List.mem_flatMap, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at h
    obtain ⟨A, hA, ⟨R, a, L1⟩, ⟨hp1, ha, htk⟩, he⟩ := h
    have e1 : S.word = R ++ a :: L1 := mem_splits_of _ _ _ _ hp1
    have ha' : a = A.xyz.1 := ha
    have htk' : L1.take 2 = [A.abc.2.1, A.xyz.2.1] := htk
    have hL1 : L1 = [A.abc.2.1, A.xyz.2.1] ++ L1.drop 2 := by
      rw [← htk']
      exact (List.take_append_drop ..).symm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine LocalArc.output S A R (L1.drop 2) hA ?_
    calc S.word = R ++ A.xyz.1 :: L1 := by rw [e1, ha']
      _ = R ++ A.xyz.1 :: ([A.abc.2.1, A.xyz.2.1] ++ L1.drop 2) := by rw [← hL1]
      _ = R ++ [A.xyz.1, A.abc.2.1, A.xyz.2.1] ++ L1.drop 2 := by simp

theorem succ_complete {S T : LocalState} {e : Option Variable} (h : LocalArc S e T) :
    (e, T) ∈ succ S := by
  cases h with
  | internal t u R X Y Z ht hc hw =>
    simp only [succ, List.mem_append]
    left; left
    simp only [succI, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
    refine ⟨t, ht, u, cyc_rots hc, (R, u.1, X ++ u.2.1 :: (Y ++ u.2.2 :: Z)),
      ⟨mem_splits_of_eq _ _ _ _ (by rw [hw]; simp), rfl⟩, (X, u.2.1, Y ++ u.2.2 :: Z),
      ⟨mem_splits_of_eq _ _ _ _ rfl, rfl⟩, (Y, u.2.2, Z),
      ⟨mem_splits_of_eq _ _ _ _ rfl, rfl⟩, rfl⟩
  | input A R U V W ha hw =>
    simp only [succ, List.mem_append]
    left; right
    simp only [succIn, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
    refine ⟨A, ha, (R, A.abc.1, U ++ A.xyz.2.2 :: (V ++ A.abc.2.2 :: W)),
      ⟨mem_splits_of_eq _ _ _ _ (by rw [hw]; simp), rfl⟩, (U, A.xyz.2.2, V ++ A.abc.2.2 :: W),
      ⟨mem_splits_of_eq _ _ _ _ rfl, rfl⟩, (V, A.abc.2.2, W),
      ⟨mem_splits_of_eq _ _ _ _ rfl, rfl⟩, rfl⟩
  | output A R Tl ha hw =>
    simp only [succ, List.mem_append]
    right
    simp only [succOut, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
    refine ⟨A, ha, (R, A.xyz.1, A.abc.2.1 :: A.xyz.2.1 :: Tl),
      ⟨mem_splits_of_eq _ _ _ _ (by rw [hw]; simp), rfl, rfl⟩, rfl⟩

def meas (S : LocalState) : ℕ :=
  2 * S.inputs.length + S.outputs.length + S.internalTriples.length

theorem arc_meas {S T : LocalState} {e : Option Variable} (h : LocalArc S e T) :
    meas T < meas S := by
  cases h with
  | internal t u R X Y Z ht hc hw =>
    have := List.length_pos_of_mem ht
    simp only [meas, List.length_erase_of_mem ht]
    omega
  | input A R U V W ha hw =>
    have := List.length_pos_of_mem ha
    simp only [meas, List.length_erase_of_mem ha, List.length_cons]
    omega
  | output A R Tl ha hw =>
    have := List.length_pos_of_mem ha
    simp only [meas, List.length_erase_of_mem ha]
    omega

def runsN : ℕ → LocalState → List (List Variable × LocalState)
  | 0, S => [([], S)]
  | n + 1, S => ([], S) :: (succ S).flatMap
      (fun p => (runsN n p.2).map (fun q => (p.1.toList ++ q.1, q.2)))

theorem runs_sound : ∀ (n : ℕ) (S : LocalState) (x : List Variable × LocalState),
    x ∈ runsN n S → LocalRun S x.1 x.2
  | 0, S, x, h => by
    simp only [runsN, List.mem_singleton] at h
    subst h
    exact LocalRun.refl S
  | n + 1, S, x, h => by
    simp only [runsN, List.mem_cons, List.mem_flatMap, List.mem_map] at h
    rcases h with rfl | ⟨⟨e, T⟩, hp, ⟨es, U⟩, hq, rfl⟩
    · exact LocalRun.refl S
    · exact LocalRun.step (succ_sound hp) (runs_sound n T (es, U) hq)

theorem runs_complete {S U : LocalState} {es : List Variable} (h : LocalRun S es U) :
    ∀ n, meas S ≤ n → (es, U) ∈ runsN n S := by
  induction h with
  | refl S0 =>
    intro n _
    cases n with
    | zero => simp [runsN]
    | succ n => simp [runsN]
  | @step S0 T0 U0 e0 es0 harc _ ih =>
    intro n hn
    have hm := arc_meas harc
    cases n with
    | zero => omega
    | succ n =>
      simp only [runsN]
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨(e0, T0), succ_complete harc,
        List.mem_map.mpr ⟨(es0, U0), ih n (by omega), rfl⟩⟩

/-! ### The renaming used for the gadget -/

def phi (w0 w1 w2 h x : ℕ) : ℕ :=
  if x % 2 = 1 then 2 * (9 * h + x / 2) + 1
  else 12 * (if x / 12 = 0 then w0 else if x / 12 = 1 then w1 else w2) + x % 12

theorem phi_inj (w0 w1 w2 h : ℕ) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2) (h12 : w1 ≠ w2) :
    InjP (fun x => x < 36) (phi w0 w1 w2 h) := by
  intro x y (hx : x < 36) (hy : y < 36) hxy
  unfold phi at hxy
  split_ifs at hxy <;> omega

end Aux_BulteauTranspositions_NPHard_property_16

open BulteauTranspositions.NPHard Aux_BulteauTranspositions_NPHard_property_16 in
theorem solution (w0 w1 w2 h : ℕ) (hw : [w0,w1,w2].Nodup)
    (order : List Variable) :
    ActivationOrder ⟨.or,w0,w1,w2⟩ h order ↔
      order = [wire w1,wire w0,wire w2] ∨
      order = [wire w2,wire w0,wire w1] ∨
      order = [wire w1,wire w2,wire w0] ∨
      order = [wire w2,wire w1,wire w0] := by
  have h01 : w0 ≠ w1 := fun e => (List.nodup_cons.mp hw).1 (by simp [e])
  have h02 : w0 ≠ w2 := fun e => (List.nodup_cons.mp hw).1 (by simp [e])
  have h12 : w1 ≠ w2 := fun e => (List.nodup_cons.mp (List.nodup_cons.mp hw).2).1 (by simp [e])
  have hinj := phi_inj w0 w1 w2 h h01 h02 h12
  have hG : Gate.localState ⟨.or, w0, w1, w2⟩ h =
      mapS (phi w0 w1 w2 h) (Gate.localState ⟨.or, 0, 1, 2⟩ 0) := by
    simp [Gate.localState, Gate.word, Gate.internals, Gate.inputs, Gate.outputs, wire, fresh,
      mapS, mapV, mapT, phi]
  have hok : SOk (fun x => x < 36) (Gate.localState ⟨.or, 0, 1, 2⟩ 0) := by
    unfold SOk VOk TOk
    decide +kernel
  have hmeas : meas (Gate.localState ⟨.or, 0, 1, 2⟩ 0) ≤ 8 := by decide +kernel
  have key : ∀ x ∈ runsN 8 (Gate.localState ⟨.or, 0, 1, 2⟩ 0), x.2.inputs = [] →
      x.2.outputs = [] → x.1 = [wire 1, wire 0, wire 2] ∨ x.1 = [wire 2, wire 0, wire 1] ∨ x.1 = [wire 1, wire 2, wire 0] ∨ x.1 = [wire 2, wire 1, wire 0] := by
    decide +kernel
  have ex0 : ∃ x ∈ runsN 8 (Gate.localState ⟨.or, 0, 1, 2⟩ 0),
      x.1 = [wire 1, wire 0, wire 2] ∧ x.2.inputs = [] ∧ x.2.outputs = [] := by
    decide +kernel
  have L0 : [wire 1, wire 0, wire 2].map (mapV (phi w0 w1 w2 h)) =
      [wire w1, wire w0, wire w2] := by
    simp [wire, mapV, mapT, phi]
  have ex1 : ∃ x ∈ runsN 8 (Gate.localState ⟨.or, 0, 1, 2⟩ 0),
      x.1 = [wire 2, wire 0, wire 1] ∧ x.2.inputs = [] ∧ x.2.outputs = [] := by
    decide +kernel
  have L1 : [wire 2, wire 0, wire 1].map (mapV (phi w0 w1 w2 h)) =
      [wire w2, wire w0, wire w1] := by
    simp [wire, mapV, mapT, phi]
  have ex2 : ∃ x ∈ runsN 8 (Gate.localState ⟨.or, 0, 1, 2⟩ 0),
      x.1 = [wire 1, wire 2, wire 0] ∧ x.2.inputs = [] ∧ x.2.outputs = [] := by
    decide +kernel
  have L2 : [wire 1, wire 2, wire 0].map (mapV (phi w0 w1 w2 h)) =
      [wire w1, wire w2, wire w0] := by
    simp [wire, mapV, mapT, phi]
  have ex3 : ∃ x ∈ runsN 8 (Gate.localState ⟨.or, 0, 1, 2⟩ 0),
      x.1 = [wire 2, wire 1, wire 0] ∧ x.2.inputs = [] ∧ x.2.outputs = [] := by
    decide +kernel
  have L3 : [wire 2, wire 1, wire 0].map (mapV (phi w0 w1 w2 h)) =
      [wire w2, wire w1, wire w0] := by
    simp [wire, mapV, mapT, phi]
  unfold ActivationOrder
  constructor
  · rintro ⟨U', hrun, hin, hout⟩
    rw [hG] at hrun
    obtain ⟨es, U, hrun0, rfl, rfl⟩ := run_pull hinj hrun _ hok rfl
    have hin0 : U.inputs = [] := by simpa [mapS] using hin
    have hout0 : U.outputs = [] := by simpa [mapS] using hout
    rcases key _ (runs_complete hrun0 8 hmeas) hin0 hout0 with e0 | e1 | e2 | e3
    · refine Or.inl ?_
      have e' : es = [wire 1, wire 0, wire 2] := e0
      rw [e', L0]
    · refine Or.inr (Or.inl ?_)
      have e' : es = [wire 2, wire 0, wire 1] := e1
      rw [e', L1]
    · refine Or.inr (Or.inr (Or.inl ?_))
      have e' : es = [wire 1, wire 2, wire 0] := e2
      rw [e', L2]
    · refine Or.inr (Or.inr (Or.inr ?_))
      have e' : es = [wire 2, wire 1, wire 0] := e3
      rw [e', L3]
  · rintro (rfl | rfl | rfl | rfl)
    · obtain ⟨x, hx, h1, h2, h3⟩ := ex0
      have hr := runs_sound _ _ x hx
      refine ⟨mapS (phi w0 w1 w2 h) x.2, ?_, by simp [mapS, h2], by simp [mapS, h3]⟩
      rw [hG, ← L0, ← h1]
      exact run_map hinj hr hok
    · obtain ⟨x, hx, h1, h2, h3⟩ := ex1
      have hr := runs_sound _ _ x hx
      refine ⟨mapS (phi w0 w1 w2 h) x.2, ?_, by simp [mapS, h2], by simp [mapS, h3]⟩
      rw [hG, ← L1, ← h1]
      exact run_map hinj hr hok
    · obtain ⟨x, hx, h1, h2, h3⟩ := ex2
      have hr := runs_sound _ _ x hx
      refine ⟨mapS (phi w0 w1 w2 h) x.2, ?_, by simp [mapS, h2], by simp [mapS, h3]⟩
      rw [hG, ← L2, ← h1]
      exact run_map hinj hr hok
    · obtain ⟨x, hx, h1, h2, h3⟩ := ex3
      have hr := runs_sound _ _ x hx
      refine ⟨mapS (phi w0 w1 w2 h) x.2, ?_, by simp [mapS, h2], by simp [mapS, h3]⟩
      rw [hG, ← L3, ← h1]
      exact run_map hinj hr hok
