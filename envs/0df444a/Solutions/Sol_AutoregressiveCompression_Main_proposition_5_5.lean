-- Prove2me | solution 1 for AutoregressiveCompression.Main.proposition_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T23:11:14.465983+00:00
-- url     : https://prove2.me/submissions/ab9b5067-1bfc-4220-bcc8-b6ed7397db39

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Tasks
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
open scoped BigOperators

namespace QMCBoolSim
open Turing Function OAI.MetricKMedian.Binary

section Sim
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Boolean statements over the extended state. -/
abbrev St (K Λ σ : Type) := TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)

/-- Push the first `n` bits of `g v`, so that bit `0` ends on top. -/
def pushAt (k : K) (g : σ × Option Bool → List Bool) : ℕ → St K Λ σ → St K Λ σ
  | 0, q => q
  | n + 1, q => .push k (fun v => (g v).getD n false) (pushAt k g n q)

theorem pushAt_spec (k : K) (g : σ × Option Bool → List Bool) (n : ℕ) (q : St K Λ σ)
    (v : σ × Option Bool) (s : K → List Bool) (hn : n ≤ (g v).length) :
    TM2.stepAux (pushAt k g n q) v s = TM2.stepAux q v (update s k ((g v).take n ++ s k)) := by
  induction n generalizing s with
  | zero => simp [pushAt]
  | succ n ih =>
      simp only [pushAt, TM2.stepAux]
      rw [ih _ (by omega)]
      have hlt : n < (g v).length := by omega
      simp only [update_self, update_idem]
      congr 2
      rw [List.getD_eq_getElem _ _ hlt, List.take_succ_eq_append_getElem hlt]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Read `n` bits from `k`, remembering them in the control flow. -/
def readTree (k : K) : ℕ → (List Bool → St K Λ σ) → St K Λ σ → St K Λ σ
  | 0, cont, _ => cont []
  | n + 1, cont, e =>
      .pop k (fun v x => (v.1, x))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => v.2 == some true)
            (readTree k n (fun l => cont (true :: l)) e)
            (readTree k n (fun l => cont (false :: l)) e))
          e)

theorem readTree_spec (k : K) (l : List Bool) (cont : List Bool → St K Λ σ) (e : St K Λ σ)
    (v : σ) (b : Option Bool) (s : K → List Bool) (rest : List Bool) (hs : s k = l ++ rest) :
    ∃ b', TM2.stepAux (readTree k l.length cont e) (v, b) s
      = TM2.stepAux (cont l) (v, b') (update s k rest) := by
  induction l generalizing cont b s with
  | nil =>
      refine ⟨b, ?_⟩
      have : update s k rest = s := by
        have : rest = s k := by simpa using hs.symm
        rw [this]; simp
      rw [this]; rfl
  | cons x l ih =>
      have hs' : s k = x :: (l ++ rest) := by simpa using hs
      cases x with
      | true =>
          obtain ⟨b', hb⟩ := ih (fun l => cont (true :: l)) (some true)
            (update s k (l ++ rest)) (by simp)
          refine ⟨b', ?_⟩
          simp only [update_idem] at hb
          simpa [List.length_cons, readTree, TM2.stepAux, hs'] using hb
      | false =>
          obtain ⟨b', hb⟩ := ih (fun l => cont (false :: l)) (some false)
            (update s k (l ++ rest)) (by simp)
          refine ⟨b', ?_⟩
          simp only [update_idem] at hb
          simpa [List.length_cons, readTree, TM2.stepAux, hs'] using hb

theorem readTree_empty (k : K) (n : ℕ) (cont : List Bool → St K Λ σ) (e : St K Λ σ)
    (v : σ) (b : Option Bool) (s : K → List Bool) (hs : s k = []) :
    TM2.stepAux (readTree k (n + 1) cont e) (v, b) s = TM2.stepAux e (v, none) s := by
  have : update s k [] = s := by rw [← hs]; simp
  simp [readTree, TM2.stepAux, hs, this]

/-- The symbols pushed by a statement. -/
def syms : TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ syms q
  | .peek _ _ q => syms q
  | .pop _ _ q => syms q
  | .load _ q => syms q
  | .branch _ q r => syms q ∪ syms r
  | .goto _ => ∅
  | .halt => ∅

theorem syms_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (syms q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek k f q ih => exact ih
  | pop k f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ihq ihr => exact ihq.union ihr
  | goto f => exact Set.finite_empty
  | halt => exact Set.finite_empty

variable (w : K → ℕ) (c : ∀ k, Γ k → List Bool) (d : ∀ k, List Bool → Option (Γ k))

/-- Translate a statement to Boolean stacks. -/
def tr : TM2.Stmt Γ Λ σ → St K Λ σ
  | .push k f q => pushAt k (fun v => c k (f v.1)) (w k) (tr q)
  | .peek k f q =>
      readTree k (w k)
        (fun l => pushAt k (fun _ => l) (w k) (.load (fun v => (f v.1 (d k l), none)) (tr q)))
        (.load (fun v => (f v.1 none, none)) (tr q))
  | .pop k f q =>
      readTree k (w k)
        (fun l => .load (fun v => (f v.1 (d k l), none)) (tr q))
        (.load (fun v => (f v.1 none, none)) (tr q))
  | .load f q => .load (fun v => (f v.1, none)) (tr q)
  | .branch f q r => .branch (fun v => f v.1) (tr q) (tr r)
  | .goto f => .goto (fun v => f v.1)
  | .halt => .halt

/-- Encode the stacks. -/
def enc (s : ∀ k, List (Γ k)) : K → List Bool := fun k => (s k).flatMap (c k)

/-- Encode a configuration. -/
def ecfg (a : TM2.Cfg Γ Λ σ) : TM2.Cfg (fun _ : K => Bool) Λ (σ × Option Bool) :=
  ⟨a.l, (a.var, none), enc c a.stk⟩

theorem enc_update (s : ∀ k, List (Γ k)) (k : K) (t : List (Γ k)) :
    enc c (update s k t) = update (enc c s) k (t.flatMap (c k)) := by
  funext j
  by_cases h : j = k
  · subst h; simp [enc]
  · simp [enc, update_of_ne h]

variable (T : Set (Σ k, Γ k))

theorem inv_update {s : ∀ k, List (Γ k)} (hs : ∀ k x, x ∈ s k → (⟨k, x⟩ : Σ k, Γ k) ∈ T)
    {k : K} {t : List (Γ k)} (ht : ∀ x ∈ t, (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    ∀ j x, x ∈ update s k t j → (⟨j, x⟩ : Σ k, Γ k) ∈ T := by
  intro j x hx
  by_cases h : j = k
  · subst h
    simp only [update_self] at hx
    exact ht x hx
  · rw [update_of_ne h] at hx
    exact hs j x hx

variable (hw : ∀ k, 0 < w k)
  (hlen : ∀ k x, (⟨k, x⟩ : Σ k, Γ k) ∈ T → (c k x).length = w k)
  (hd : ∀ k x, (⟨k, x⟩ : Σ k, Γ k) ∈ T → d k (c k x) = some x)

include hw hlen hd in
theorem tr_spec (q : TM2.Stmt Γ Λ σ) (hq : syms q ⊆ T) (v : σ) (s : ∀ k, List (Γ k))
    (hs : ∀ k x, x ∈ s k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    TM2.stepAux (tr w c d q) (v, none) (enc c s) = ecfg c (TM2.stepAux q v s) ∧
      (∀ k x, x ∈ (TM2.stepAux q v s).stk k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) := by
  induction q generalizing v s with
  | push k f q ih =>
      have hfv : (⟨k, f v⟩ : Σ k, Γ k) ∈ T := hq (Or.inl ⟨v, rfl⟩)
      have hs' := inv_update T hs (k := k) (t := f v :: s k) (by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hfv
        · exact hs k x hx)
      have ih' := ih (fun _ hx => hq (Or.inr hx)) v _ hs'
      simp only [tr, TM2.stepAux]
      refine ⟨?_, ih'.2⟩
      rw [pushAt_spec _ _ _ _ _ _ (by simp [hlen k _ hfv]), ← ih'.1, enc_update]
      congr 2
      rw [List.take_of_length_le (by simp [hlen k _ hfv])]
      simp [enc]
  | peek k f q ih =>
      have hq' : syms q ⊆ T := hq
      simp only [tr, TM2.stepAux]
      cases hsk : s k with
      | nil =>
          have ih' := ih hq' (f v none) s hs
          refine ⟨?_, ih'.2⟩
          obtain ⟨n, hn⟩ : ∃ n, w k = n + 1 := Nat.exists_eq_succ_of_ne_zero (hw k).ne'
          rw [hn, readTree_empty _ _ _ _ _ _ _ (by simp [enc, hsk])]
          simpa [TM2.stepAux] using ih'.1
      | cons x t =>
          have hx : (⟨k, x⟩ : Σ k, Γ k) ∈ T := hs k x (by simp [hsk])
          have ih' := ih hq' (f v (some x)) s hs
          refine ⟨?_, ih'.2⟩
          obtain ⟨b', hb⟩ := readTree_spec (Λ := Λ) k (c k x)
            (fun l => pushAt k (fun _ => l) (w k) (.load (fun v => (f v.1 (d k l), none))
              (tr w c d q)))
            (.load (fun v => (f v.1 none, none)) (tr w c d q)) v none (enc c s)
            (t.flatMap (c k)) (by simp [enc, hsk])
          rw [hlen k x hx] at hb
          simp only [List.head?_cons]
          rw [hb]
          rw [pushAt_spec _ _ _ _ _ _ (by simp [hlen k _ hx]),
            List.take_of_length_le (by simp [hlen k _ hx])]
          simp only [TM2.stepAux, hd k x hx, update_idem, update_self]
          have : update (enc c s) k (c k x ++ t.flatMap (c k)) = enc c s := by
            have : c k x ++ t.flatMap (c k) = enc c s k := by simp [enc, hsk]
            rw [this]; simp
          rw [this]
          exact ih'.1
  | pop k f q ih =>
      have hq' : syms q ⊆ T := hq
      simp only [tr, TM2.stepAux]
      cases hsk : s k with
      | nil =>
          have hup : update s k [] = s := by rw [← hsk]; simp
          have ih' := ih hq' (f v none) s hs
          simp only [List.tail_nil, List.head?_nil, hup]
          refine ⟨?_, ih'.2⟩
          obtain ⟨n, hn⟩ : ∃ n, w k = n + 1 := Nat.exists_eq_succ_of_ne_zero (hw k).ne'
          rw [hn, readTree_empty _ _ _ _ _ _ _ (by simp [enc, hsk])]
          simpa [TM2.stepAux] using ih'.1
      | cons x t =>
          have hx : (⟨k, x⟩ : Σ k, Γ k) ∈ T := hs k x (by simp [hsk])
          have hs' := inv_update T hs (k := k) (t := t) (by
            intro y hy
            exact hs k y (by simp [hsk, hy]))
          have ih' := ih hq' (f v (some x)) _ hs'
          simp only [List.tail_cons, List.head?_cons]
          refine ⟨?_, ih'.2⟩
          obtain ⟨b', hb⟩ := readTree_spec (Λ := Λ) k (c k x)
            (fun l => .load (fun v => (f v.1 (d k l), none)) (tr w c d q))
            (.load (fun v => (f v.1 none, none)) (tr w c d q)) v none (enc c s)
            (t.flatMap (c k)) (by simp [enc, hsk])
          rw [hlen k x hx] at hb
          rw [hb]
          simp only [TM2.stepAux, hd k x hx]
          rw [← enc_update]
          exact ih'.1
  | load f q ih =>
      have ih' := ih hq (f v) s hs
      simp only [tr, TM2.stepAux]
      exact ih'
  | branch f q r ihq ihr =>
      have hq' : syms q ⊆ T := fun _ hx => hq (Or.inl hx)
      have hr' : syms r ⊆ T := fun _ hx => hq (Or.inr hx)
      simp only [tr, TM2.stepAux]
      cases hf : f v with
      | false => simpa using ihr hr' v s hs
      | true => simpa using ihq hq' v s hs
  | goto f =>
      exact ⟨rfl, hs⟩
  | halt =>
      exact ⟨rfl, hs⟩

include hw hlen hd in
theorem sim_trace (m : Λ → TM2.Stmt Γ Λ σ) (hm : ∀ l, syms (m l) ⊆ T)
    {n : ℕ} {a b : TM2.Cfg Γ Λ σ} (h : Trace (TM2.step m) n a b)
    (ha : ∀ k x, x ∈ a.stk k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    Trace (TM2.step (fun l => tr w c d (m l))) n (ecfg c a) (ecfg c b) := by
  induction h with
  | refl => exact Trace.refl _
  | @cons n a b e hab _ ih =>
      rcases a with ⟨l, v, s⟩
      cases l with
      | none => cases hab
      | some l =>
          have hb : b = TM2.stepAux (m l) v s := (Option.some.inj hab).symm
          subst b
          have hspec := tr_spec w c d T hw hlen hd (m l) (hm l) v s ha
          refine Trace.cons ?_ (ih hspec.2)
          exact congrArg some hspec.1

end Sim

theorem exists_block (A : Type) (S : Set A) (hS : S.Finite) :
    ∃ (w : ℕ) (c : A → List Bool), 0 < w ∧ (∀ x ∈ S, (c x).length = w) ∧ Set.InjOn c S := by
  classical
  haveI : Finite S := hS
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  let i : A → ℕ := fun x => if h : x ∈ S then (e ⟨x, h⟩).val else 0
  refine ⟨n + 1, fun x => List.ofFn (fun j : Fin (n + 1) => decide (j.val = i x)),
    Nat.succ_pos _, fun x _ => by simp, ?_⟩
  intro x hx y hy hxy
  have hxy' := List.ofFn_injective hxy
  have hix : i x < n + 1 := by
    have : i x = (e ⟨x, hx⟩).val := by simp [i, hx]
    have := (e ⟨x, hx⟩).isLt
    omega
  have h1 := congrFun hxy' ⟨i x, hix⟩
  simp only [decide_true] at h1
  have h2 : i x = i y := by simpa using h1.symm
  have h3 : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
    apply Fin.ext
    simpa [i, hx, hy] using h2
  simpa using e.injective h3

/-- The Boolean machine simulating a bundled machine. -/
abbrev simMachine (tm : FinTM2) (w : tm.K → ℕ) (c : ∀ k, tm.Γ k → List Bool)
    (d : ∀ k, List Bool → Option (tm.Γ k)) : Machine :=
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  { K := tm.K
    input := tm.k₀
    output := tm.k₁
    Label := tm.Λ
    main := tm.main
    State := tm.σ × Option Bool
    initial := (tm.initialState, none)
    code := fun l => tr w c d (tm.m l) }

theorem simulate (tm : FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) :
    ∃ (M : Machine) (τ : Bool ≃ Bool), ∀ (s t : List Bool) (n : ℕ),
      TM2OutputsInTime tm (s.map e₀.symm) (some (t.map e₁.symm)) n →
        Nonempty (TM2OutputsInTime M.tm s (some (t.map τ)) n) := by
  classical
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  let T : Set (Σ k, tm.Γ k) :=
    (⋃ l, syms (tm.m l)) ∪ Set.range (fun x : tm.Γ tm.k₀ => (⟨tm.k₀, x⟩ : Σ k, tm.Γ k))
  haveI : Finite (tm.Γ tm.k₀) := Finite.of_equiv Bool e₀.symm
  have hT : T.Finite :=
    (Set.finite_iUnion fun l => syms_finite (tm.m l)).union (Set.finite_range _)
  have key : ∀ k, ∃ (w : ℕ) (c : tm.Γ k → List Bool), 0 < w ∧
      (∀ x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → (c x).length = w) ∧
      (∀ x y, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → (⟨k, y⟩ : Σ k, tm.Γ k) ∈ T → c x = c y → x = y) ∧
      (∀ h : k = tm.k₀, ∀ x, c x = [e₀ (h ▸ x)]) ∧
      (k ≠ tm.k₀ → ∀ h : k = tm.k₁, ∀ x, c x = [e₁ (h ▸ x)]) := by
    intro k
    by_cases h0 : k = tm.k₀
    · subst h0
      refine ⟨1, fun x => [e₀ x], one_pos, fun _ _ => rfl, ?_, fun _ _ => rfl, fun h => absurd rfl h⟩
      intro x y _ _ hxy
      exact e₀.injective (by simpa using hxy)
    · by_cases h1 : k = tm.k₁
      · subst h1
        refine ⟨1, fun x => [e₁ x], one_pos, fun _ _ => rfl, ?_, fun h => absurd h h0,
          fun _ _ _ => rfl⟩
        intro x y _ _ hxy
        exact e₁.injective (by simpa using hxy)
      · have hS : {x : tm.Γ k | (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T}.Finite :=
          hT.preimage (f := fun x : tm.Γ k => (⟨k, x⟩ : Σ k, tm.Γ k))
            (sigma_mk_injective.injOn)
        obtain ⟨w, c, hw, hl, hi⟩ := exists_block _ _ hS
        exact ⟨w, c, hw, hl, fun x y hx hy h => hi hx hy h, fun h => absurd h h0,
          fun _ h => absurd h h1⟩
  choose w c hw hlen hinj hc0 hc1 using key
  let d : ∀ k, List Bool → Option (tm.Γ k) := fun k l =>
    if h : ∃ x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T ∧ c k x = l then some h.choose else none
  have hd : ∀ k x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → d k (c k x) = some x := by
    intro k x hx
    have h : ∃ y, (⟨k, y⟩ : Σ k, tm.Γ k) ∈ T ∧ c k y = c k x := ⟨x, hx, rfl⟩
    have hspec := h.choose_spec
    simp only [d, dif_pos h]
    exact congrArg some (hinj k _ _ hspec.1 hx hspec.2)
  have hc0' : ∀ x, c tm.k₀ x = [e₀ x] := fun x => hc0 tm.k₀ rfl x
  obtain ⟨τ, hτ⟩ : ∃ τ : Bool ≃ Bool, ∀ x, c tm.k₁ x = [τ (e₁ x)] := by
    by_cases h : tm.k₁ = tm.k₀
    · have aux : ∀ k (_ : k = tm.k₀) (e : tm.Γ k ≃ Bool),
          ∃ τ : Bool ≃ Bool, ∀ x, c k x = [τ (e x)] := by
        intro k hk e
        subst hk
        exact ⟨e.symm.trans e₀, fun x => by simp [hc0']⟩
      exact aux _ h e₁
    · exact ⟨Equiv.refl _, fun x => hc1 tm.k₁ h rfl x⟩
  have hin : ∀ s : List Bool, (s.map e₀.symm).flatMap (c tm.k₀) = s := by
    intro s
    induction s with
    | nil => rfl
    | cons b s ih => simpa [hc0'] using ih
  have hout : ∀ t : List Bool, (t.map e₁.symm).flatMap (c tm.k₁) = t.map τ := by
    intro t
    induction t with
    | nil => rfl
    | cons b t ih => simpa [hτ] using ih
  refine ⟨simMachine tm w c d, τ, ?_⟩
  intro s t n h
  have htr : Trace (TM2.step tm.m) h.steps _ _ := Trace.of_iterate (f := tm.step) h.evals_in_steps
  have hsim := sim_trace w c d T hw hlen hd tm.m
    (fun l x hx => Or.inl (Set.mem_iUnion.2 ⟨l, hx⟩)) htr (by
      intro k x hx
      by_cases hk : k = tm.k₀
      · subst hk
        exact Or.inr ⟨_, rfl⟩
      · simp [initList, hk] at hx)
  have hinit : ecfg c (initList tm (s.map e₀.symm)) = (simMachine tm w c d).initialCfg s := by
    refine congrArg (TM2.Cfg.mk _ _) ?_
    funext k
    by_cases hk : k = tm.k₀
    · subst hk
      simpa [enc, initList, Machine.initialCfg] using hin s
    · simp [enc, initList, Machine.initialCfg, hk]
  have hhalt : ecfg c (haltList tm (t.map e₁.symm)) = (simMachine tm w c d).finalCfg (t.map τ) := by
    refine congrArg (TM2.Cfg.mk _ _) ?_
    funext k
    by_cases hk : k = tm.k₁
    · subst hk
      simpa [enc, haltList, Machine.finalCfg] using hout t
    · simp [enc, haltList, Machine.finalCfg, hk]
  rw [hinit, hhalt] at hsim
  exact ⟨⟨⟨_, hsim.iterate_eq⟩, h.steps_le_m⟩⟩

/-- A letterwise transducer. -/
def mapT (τ : Bool → Bool) : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((), [τ b])
  finish _ := []

theorem mapT_run (τ : Bool → Bool) (xs : List Bool) : (mapT τ).run () xs = xs.map τ := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change τ b :: (mapT τ).run () xs = τ b :: xs.map τ; rw [ih]

end QMCBoolSim

namespace AC55
open AutoregressiveCompression.Main OAI.MetricKMedian.Binary Turing
open scoped Classical

noncomputable section

/-! ## Parsing frames -/

def unframeAux : Bits → Bits → List Bits
  | acc, b₁ :: b₂ :: rest =>
      if b₁ = b₂ then unframeAux (b₁ :: acc) rest else acc.reverse :: unframeAux [] rest
  | _, _ => []

def unframe (x : Bits) : List Bits := unframeAux [] x

theorem unframeAux_dbl (acc b rest : Bits) :
    unframeAux acc (b.flatMap (fun x => [x, x]) ++ [false, true] ++ rest) =
      (acc.reverse ++ b) :: unframeAux [] rest := by
  induction b generalizing acc with
  | nil => simp [unframeAux]
  | cons x b ih =>
      have := ih (x :: acc)
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at this ⊢
      rw [unframeAux, if_pos rfl]
      simpa using this

theorem unframe_frame (l : List Bits) : unframe (frame l) = l := by
  induction l with
  | nil => simp [unframe, frame, unframeAux]
  | cons b bs ih =>
      simp only [unframe, frame] at ih ⊢
      rw [unframeAux_dbl, ih]
      simp

/-! ## Squashing a rational into `[0,1]` -/

def squash (q : ℚ) : ℚ := if q < 0 then 0 else q / (1 + q)

theorem squash_nonneg (q : ℚ) : 0 ≤ squash q := by
  unfold squash; split_ifs with h
  · exact le_rfl
  · push_neg at h; positivity

theorem squash_le_one (q : ℚ) : squash q ≤ 1 := by
  unfold squash; split_ifs with h
  · norm_num
  · push_neg at h; rw [div_le_one (by linarith)]; linarith

/-! ## The tester -/

def parA (ρ : MvPolynomial (Fin 3) ℕ) (n m : ℕ) : ℕ :=
  Nat.findGreatest (fun j => eval3 ρ n j j ≤ m) (m + 2)

theorem bitsValue_natBits (k : ℕ) : bitsValue (natBits k) = k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [natBits, bitsValue]
    · have h := ih (k / 2) (Nat.div_lt_self hk (by norm_num))
      unfold natBits at h ⊢
      rw [Nat.digits_def' (by norm_num) hk]
      simp only [List.map_cons, bitsValue, h]
      rcases Nat.mod_two_eq_zero_or_one k with h2 | h2 <;> simp [h2] <;> omega
theorem squash_num_den (q : ℚ) (hq : 0 ≤ q) :
    (q / (1 + q)).num = q.num ∧ (q / (1 + q)).den = q.num.natAbs + q.den := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hq' : q / (1 + q) = ((q.num : ℤ) : ℚ) / ((q.num + q.den : ℤ) : ℚ) := by
    have hd : (q.den : ℚ) ≠ 0 := by positivity
    rw [← Rat.num_div_den q]
    simp only [Rat.num_div_den]
    push_cast
    field_simp
    linear_combination (Rat.mul_den_eq_num q)
  have hb : (0 : ℤ) < q.num + q.den := by have := q.den_pos; omega
  have hc : Nat.Coprime q.num.natAbs (q.num + q.den : ℤ).natAbs := by
    have : (q.num + q.den : ℤ).natAbs = q.num.natAbs + q.den := by omega
    rw [this]
    exact Nat.coprime_self_add_right.mpr q.reduced
  refine ⟨?_, ?_⟩
  · rw [hq', Rat.num_div_eq_of_coprime hb hc]
  · rw [hq']
    have := Rat.den_div_eq_of_coprime hb hc
    omega


/-! ## Post-processing as a polynomial-time Boolean program -/

def compT (j : ℕ) : Transducer where
  Q := Fin (j + 2) × Option Bool
  initial := (0, none)
  next q b := match q.2 with
    | none => ((q.1, some b), [])
    | some p => if p = b then ((q.1, none), if q.1.val = j then [p] else [])
        else ((⟨min (q.1.val + 1) (j + 1), by omega⟩, none), [])
  finish _ := []

theorem compT_dbl (j : ℕ) (u rest : Bits) (i : Fin (j + 2)) :
    (compT j).run (i, none) (u.flatMap (fun x => [x, x]) ++ [false, true] ++ rest) =
      (if i.val = j then u else []) ++
        (compT j).run (⟨min (i.val + 1) (j + 1), by omega⟩, none) rest := by
  have step1 : ∀ (x : Bool) (rest : Bits), (compT j).run (i, none) (x :: x :: rest) =
      (if i.val = j then [x] else []) ++ (compT j).run (i, none) rest := by
    intro x rest; simp [Transducer.run, compT]
  have step2 : ∀ rest : Bits, (compT j).run (i, none) (false :: true :: rest) =
      (compT j).run (⟨min (i.val + 1) (j + 1), by omega⟩, none) rest := by
    intro rest; simp [Transducer.run, compT]
  induction u with
  | nil => simpa using step2 rest
  | cons x u ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
      rw [step1, ih]
      split_ifs <;> simp

theorem compT_frame (j : ℕ) (l : List Bits) (i : Fin (j + 2)) :
    (compT j).run (i, none) (frame l) = if i.val ≤ j then l.getD (j - i.val) [] else [] := by
  induction l generalizing i with
  | nil => simp [frame, Transducer.run, compT]
  | cons b bs ih =>
      simp only [frame]
      rw [compT_dbl, ih]
      by_cases h1 : i.val = j
      · simp [h1]
      · by_cases h2 : i.val ≤ j
        · have h3 : min (i.val + 1) (j + 1) ≤ j := by omega
          have h4 : j - i.val = (j - min (i.val + 1) (j + 1)) + 1 := by omega
          simp only [h1, if_false, List.nil_append, if_pos h3, if_pos h2, h4,
            List.getD_cons_succ]
        · have h3 : ¬ min (i.val + 1) (j + 1) ≤ j := by omega
          simp only [h1, h2, h3, if_false, List.nil_append]

def comp (j : ℕ) (z : Bits) : Bits := (compT j).run (compT j).initial z

theorem comp_frame (j : ℕ) (l : List Bits) : comp j (frame l) = l.getD j [] := by
  unfold comp
  rw [show (compT j).initial = ((0 : Fin (j + 2)), none) from rfl, compT_frame]
  simp

theorem comp_poly (j : ℕ) : Automatic.Poly (comp j) :=
  ⟨((BooleanLists.unpackProgram.comp (compT j).program).comp BooleanLists.packProgram).congr _
    (fun _ => rfl)⟩

theorem natBitsT_poly : Automatic.Poly (Nat.bits : ℕ → List Bool) :=
  ⟨BooleanLists.packProgram.recode Nat.bits (fun _ => rfl) (fun _ => rfl)⟩

theorem value_poly : Automatic.Poly Word.value := ⟨BooleanLists.valueProgram⟩

def frameT (l : List Bits) : Bits := l.flatMap fun b => b.flatMap (fun x => [x, x]) ++ [false, true]

theorem frameT_eq (l : List Bits) : frameT l = frame l := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp only [frameT, List.flatMap_cons] at ih ⊢; rw [ih]; simp [frame]

def postG (z : Bits) : Bits :=
  if (comp 0 z)[0]?.getD false then ratBits 0
  else frameT [[false], comp 1 z, Nat.bits (Word.value (comp 1 z) + Word.value (comp 2 z))]

theorem dbl_poly : Automatic.Poly (fun b : Bits => b.flatMap (fun x => [x, x])) := by
  have h : Automatic.Poly (fun p : Bits × Bool => [p.2, p.2]) := by fun_prop
  exact Automatic.Poly.list_flatMap (f := fun (_ : Bits) (x : Bool) => [x, x]) (as := id) h Automatic.Poly.identity
theorem frameT_poly : Automatic.Poly frameT := by
  unfold frameT
  have h : Automatic.Poly (fun p : List Bits × Bits => p.2.flatMap (fun x => [x, x]) ++ [false, true]) := by
    have := dbl_poly
    fun_prop
  exact Automatic.Poly.list_flatMap (f := fun (_ : List Bits) (b : Bits) => b.flatMap (fun x => [x, x]) ++ [false, true]) (as := id) h Automatic.Poly.identity
theorem postG_poly : Automatic.Poly postG := by
  have h0 := comp_poly 0
  have h1 := comp_poly 1
  have h2 := comp_poly 2
  have hb := natBitsT_poly
  have hv := value_poly
  have hf := frameT_poly
  unfold postG
  fun_prop

def postFn (τ : Bool ≃ Bool) (y : Bits) : Bits := postG (y.map τ.symm)

theorem post_poly (τ : Bool ≃ Bool) :
    Nonempty (PolyProgram (id : Bits → Bits) id (postFn τ)) :=
  ⟨((((QMCBoolSim.mapT τ.symm).program.comp BooleanLists.packProgram).comp
      postG_poly.program).comp BooleanLists.unpackProgram).congr _ (fun y => by
    simp only [Function.comp, id, postFn]
    show postG ((QMCBoolSim.mapT τ.symm).run () y) = _
    rw [QMCBoolSim.mapT_run])⟩

/-! ## Pre-processing as a polynomial-time Boolean program -/

def sepT : Transducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some b, [])
    | some p => (none, if p = b then [] else [true])
  finish _ := []

theorem sepT_dbl (u rest : Bits) :
    sepT.run none (u.flatMap (fun x => [x, x]) ++ [false, true] ++ rest) =
      true :: sepT.run none rest := by
  induction u with
  | nil => simp [Transducer.run, sepT]
  | cons x u ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
      simp only [Transducer.run, sepT, if_pos rfl, List.nil_append] at ih ⊢
      exact ih

theorem sepT_frame (l : List Bits) : sepT.run none (frame l) = List.replicate l.length true := by
  induction l with
  | nil => simp [frame, Transducer.run, sepT]
  | cons b bs ih => simp only [frame]; rw [sepT_dbl, ih]; simp [List.replicate_succ]

def marks (z : Bits) : Bits := sepT.run sepT.initial z

theorem marks_frame (l : List Bits) : marks (frame l) = List.replicate l.length true :=
  sepT_frame l

theorem marks_poly : Automatic.Poly marks :=
  ⟨((BooleanLists.unpackProgram.comp sepT.program).comp BooleanLists.packProgram).congr _
    (fun _ => rfl)⟩

def stepOp (x : (ℕ × (Bits × Bits)) × (ℕ × Bool)) : ℕ × (Bits × Bits) :=
  if x.1.1 < x.2.1 then
    if x.1.2.1.isEmpty then (x.1.1, ([x.2.2], x.1.2.2))
    else if ((x.1.2.1[0]?.getD false) && x.2.2) || (!(x.1.2.1[0]?.getD false) && !x.2.2) then
      (x.1.1, ([], x.1.2.2 ++ [x.2.2, x.2.2]))
    else (x.1.1 + 1, ([], x.1.2.2 ++ [x.1.2.1[0]?.getD false, x.2.2]))
  else x.1

theorem stepOp_poly : Automatic.Poly stepOp := by
  unfold stepOp
  fun_prop

theorem enc_state_length (s : ℕ × (Bits × Bits)) :
    (Automatic.enc s).length =
      2 * s.1.bits.length + 1 + (2 * (3 * s.2.1.length) + 1 + 3 * s.2.2.length) := by
  show (encodePair Nat.bits (encodePair (encodeList encodeBool) (encodeList encodeBool)) s).length = _
  simp only [encodePair_length, BooleanLists.length]

theorem stepOp_growth (s : ℕ × (Bits × Bits)) (a : ℕ × Bool) :
    (Automatic.enc (stepOp (s, a))).length ≤
      (Automatic.enc s).length + 6 * (2 * (Automatic.enc a).length + 1) := by
  rw [enc_state_length, enc_state_length]
  have hadd := NatBinary.add_length s.1 1
  have h1 : (1 : ℕ).bits.length = 1 := by decide
  unfold stepOp
  dsimp only
  split_ifs with h₁ h₂ h₃
  · simp; omega
  · have : s.2.1.length ≠ 0 := by
      intro h; simp [List.isEmpty_iff, List.length_eq_zero_iff.mp h] at h₂
    simp; omega
  · have : s.2.1.length ≠ 0 := by
      intro h; simp [List.isEmpty_iff, List.length_eq_zero_iff.mp h] at h₂
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · omega

theorem fold_poly : Automatic.Poly (fun x : List (ℕ × Bool) × (ℕ × (Bits × Bits)) =>
    x.1.foldl (fun b a => stepOp (b, a)) x.2) :=
  ⟨stepOp_poly.program.listFoldLinear default 6 stepOp_growth⟩

def takeComps (K : ℕ) (u : Bits) : Bits :=
  ((u.map fun b => (K, b)).foldl (fun s a => stepOp (s, a)) (0, ([], []))).2.2

theorem takeComps_poly : Automatic.Poly (fun x : ℕ × Bits => takeComps x.1 x.2) := by
  unfold takeComps
  have hf := fold_poly
  have hm : Automatic.Poly (fun x : ℕ × Bits => x.2.map fun b => (x.1, b)) := by fun_prop
  have hp : Automatic.Poly (fun x : ℕ × Bits => ((x.2.map fun b => (x.1, b)),
      ((0 : ℕ), (([] : Bits), ([] : Bits))))) := Automatic.Poly.pair hm (Automatic.Poly.const _)
  have hc := Automatic.Poly.comp hf hp
  exact Automatic.Poly.comp (Automatic.Poly.snd) (Automatic.Poly.comp Automatic.Poly.snd hc)

theorem stepOp_frozen (K c : ℕ) (buf out : Bits) (hc : K ≤ c) (rest : Bits) :
    (rest.map fun b => (K, b)).foldl (fun s a => stepOp (s, a)) (c, (buf, out)) =
      (c, (buf, out)) := by
  induction rest with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.map_cons, List.foldl_cons]
      have : stepOp ((c, (buf, out)), (K, b)) = (c, (buf, out)) := by
        unfold stepOp; simp only; rw [if_neg (by omega)]
      rw [this, ih]

theorem stepOp_dbl (K c : ℕ) (out u rest : Bits) (hc : c < K) :
    ((u.flatMap (fun x => [x, x]) ++ [false, true] ++ rest).map fun b => (K, b)).foldl
        (fun s a => stepOp (s, a)) (c, ([], out)) =
      (rest.map fun b => (K, b)).foldl (fun s a => stepOp (s, a))
        (c + 1, ([], out ++ (u.flatMap (fun x => [x, x]) ++ [false, true]))) := by
  induction u generalizing out with
  | nil =>
      simp only [List.flatMap_nil, List.nil_append, List.cons_append, List.map_cons,
        List.foldl_cons]
      congr 1
      simp [stepOp, hc]
  | cons x u ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc,
        List.map_cons, List.foldl_cons] at ih ⊢
      have e : stepOp (stepOp ((c, ([], out)), (K, x)), (K, x)) = (c, ([], out ++ [x, x])) := by
        cases x <;> simp [stepOp, hc]
      rw [e, ih]
      simp

theorem takeComps_aux (K : ℕ) (l : List Bits) :
    ∀ (c : ℕ) (out : Bits), c ≤ K →
      (((frame l).map fun b => (K, b)).foldl (fun s a => stepOp (s, a)) (c, ([], out))).2.2 =
        out ++ frame (l.take (K - c)) := by
  induction l with
  | nil => intro c out _; simp [frame]
  | cons b bs ih =>
      intro c out hc
      rcases hc.lt_or_eq with hlt | heq
      · simp only [frame]
        rw [stepOp_dbl K c out b (frame bs) hlt, ih (c + 1) _ hlt]
        have : K - c = (K - (c + 1)) + 1 := by omega
        rw [this, List.take_succ_cons]
        simp [frame]
      · subst heq
        rw [stepOp_frozen c c [] out le_rfl]
        simp [frame]

theorem takeComps_frame (K : ℕ) (l : List Bits) : takeComps K (frame l) = frame (l.take K) := by
  unfold takeComps
  have := takeComps_aux K l 0 [] (Nat.zero_le K)
  simpa using this

theorem mv_eval_poly {k : ℕ} (p : MvPolynomial (Fin k) ℕ) {α : Type} [Automatic.Coding α]
    (v : α → Fin k → ℕ) (hv : ∀ i, Automatic.Poly (fun x => v x i)) :
    Automatic.Poly (fun x => MvPolynomial.eval (v x) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using Automatic.Poly.const (α := α) a
  | add p q hp hq =>
      simp only [map_add]
      exact Automatic.Poly.comp Automatic.Poly.nat_add (Automatic.Poly.pair hp hq)
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact Automatic.Poly.comp Automatic.Poly.nat_mul (Automatic.Poly.pair hp (hv i))

theorem eval3_poly (ρ : MvPolynomial (Fin 3) ℕ) {α : Type} [Automatic.Coding α]
    {a b c : α → ℕ} (ha : Automatic.Poly a) (hb : Automatic.Poly b) (hc : Automatic.Poly c) :
    Automatic.Poly (fun x => eval3 ρ (a x) (b x) (c x)) := by
  unfold eval3
  apply mv_eval_poly ρ (fun x => ![a x, b x, c x])
  intro i; fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa using hc

theorem findGreatest_eq_findIdx (P : ℕ → Prop) [DecidablePred P] (k : ℕ) :
    Nat.findGreatest P k = k - (List.range (k + 1)).findIdx (fun i => decide (P (k - i))) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.findGreatest_succ, List.range_succ_eq_map, List.findIdx_cons]
      by_cases h : P (k + 1)
      · simp [h]
      · simp only [h, if_false, Nat.sub_zero, decide_false, cond_false, List.findIdx_map]
        rw [ih]
        have : (fun i => decide (P (k + 1 - i))) ∘ Nat.succ = fun i => decide (P (k - i)) := by
          funext i; simp [Nat.succ_sub_succ]
        rw [this]
        omega

def mOf (x : Bits) : ℕ := (marks (comp 1 x)).length
def padOf (x : Bits) : Bits := marks (comp 1 x) ++ [true, true, true]
def AOf (ρ : MvPolynomial (Fin 3) ℕ) (x : Bits) : ℕ :=
  mOf x + 2 - (List.range (padOf x).length).findIdx
    (fun i => decide (eval3 ρ (comp 0 x).length (mOf x + 2 - i) (mOf x + 2 - i) ≤ mOf x))

def preFn (ρ r : MvPolynomial (Fin 3) ℕ) (z₀ : Bits) (x : Bits) : Bits :=
  if eval3 ρ (comp 0 x).length 2 2 ≤ mOf x then
    frameT [comp 0 x, (padOf x).take (AOf ρ x), (padOf x).take (AOf ρ x),
      takeComps (eval3 ρ (comp 0 x).length (AOf ρ x) (AOf ρ x)) (comp 1 x),
      (comp 2 x).take (eval3 r (comp 0 x).length (AOf ρ x) (AOf ρ x))]
  else z₀

theorem preFn_poly (ρ r : MvPolynomial (Fin 3) ℕ) (z₀ : Bits) : Automatic.Poly (preFn ρ r z₀) := by
  have h0 := comp_poly 0
  have h1 := comp_poly 1
  have h2 := comp_poly 2
  have hmk := marks_poly
  have hf := frameT_poly
  have htc := takeComps_poly
  have hn : Automatic.Poly (fun x : Bits => (comp 0 x).length) := by fun_prop
  have hm : Automatic.Poly mOf := by unfold mOf; fun_prop
  have hpad : Automatic.Poly padOf := by unfold padOf; fun_prop
  have hidx : Automatic.Poly (fun x : Bits => List.range (padOf x).length) := by
    exact Automatic.Poly.comp (f := fun xs : Bits => List.range xs.length)
      Automatic.Poly.list_indices hpad
  have hpred : Automatic.Poly (fun y : Bits × ℕ =>
      decide (eval3 ρ (comp 0 y.1).length (mOf y.1 + 2 - y.2) (mOf y.1 + 2 - y.2) ≤ mOf y.1)) := by
    have hs : Automatic.Poly (fun y : Bits × ℕ => mOf y.1 + 2 - y.2) := by fun_prop
    have he := eval3_poly ρ (a := fun y : Bits × ℕ => (comp 0 y.1).length) (by fun_prop) hs hs
    fun_prop
  have hA : Automatic.Poly (AOf ρ) := by
    unfold AOf
    have hfi := Automatic.Poly.list_findIdx (f := fun (x : Bits) (i : ℕ) =>
      decide (eval3 ρ (comp 0 x).length (mOf x + 2 - i) (mOf x + 2 - i) ≤ mOf x)) hpred hidx
    fun_prop
  have hK := eval3_poly ρ hn hA hA
  have hR := eval3_poly r hn hA hA
  have hg := eval3_poly ρ hn (Automatic.Poly.const (α := Bits) 2) (Automatic.Poly.const (α := Bits) 2)
  have ht1 : Automatic.Poly (fun x => (padOf x).take (AOf ρ x)) :=
    Automatic.Poly.comp (f := fun y : Bits × ℕ => y.1.take y.2) QMCNumericRuntime.parser_take_poly
      (Automatic.Poly.pair hpad hA)
  have ht2 : Automatic.Poly (fun x => (comp 2 x).take
      (eval3 r (comp 0 x).length (AOf ρ x) (AOf ρ x))) :=
    Automatic.Poly.comp (f := fun y : Bits × ℕ => y.1.take y.2) QMCNumericRuntime.parser_take_poly
      (Automatic.Poly.pair h2 hR)
  have ht3 : Automatic.Poly (fun x => takeComps
      (eval3 ρ (comp 0 x).length (AOf ρ x) (AOf ρ x)) (comp 1 x)) :=
    Automatic.Poly.comp (f := fun y : ℕ × Bits => takeComps y.1 y.2) htc (Automatic.Poly.pair hK h1)
  unfold preFn
  fun_prop

theorem pre_poly (ρ r : MvPolynomial (Fin 3) ℕ) (z₀ : Bits) :
    Nonempty (PolyProgram (id : Bits → Bits) id (preFn ρ r z₀)) :=
  ⟨((BooleanLists.packProgram.comp (preFn_poly ρ r z₀).program).comp
      BooleanLists.unpackProgram).congr _ (fun _ => rfl)⟩

theorem value_eq_bitsValue (l : Bits) : Word.value l = bitsValue l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [bitsValue, ih]

theorem natBits_eq_bits (k : ℕ) : Nat.bits k = natBits k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [natBits]
    · unfold natBits
      rw [Nat.digits_def' (by norm_num) hk]
      obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' k
      · have ht : t ≠ 0 := by omega
        rw [Nat.bit0_bits t ht, ih t (by omega)]
        simp [natBits, Nat.mul_mod_right, Nat.mul_div_cancel_left t (by norm_num : 0 < 2)]
      · rw [Nat.bit1_bits, ih t (by omega)]
        have h1 : (2 * t + 1) % 2 = 1 := by omega
        have h2 : (2 * t + 1) / 2 = t := by omega
        simp [natBits, h1, h2]

theorem post_correct (τ : Bool ≃ Bool) (q : ℚ) :
    postFn τ ((ratBits q).map τ) = ratBits (squash q) := by
  have hmap : ((ratBits q).map τ).map τ.symm = ratBits q := by
    simp [List.map_map]
  have hr : ratBits q = frame [[decide (q < 0)], natBits q.num.natAbs, natBits q.den] := rfl
  unfold postFn
  rw [hmap, hr]
  unfold postG
  simp only [comp_frame, List.getD_cons_zero, List.getD_cons_succ, List.getElem?_cons_zero,
    Option.getD_some]
  by_cases hq : q < 0
  · simp [hq, squash]
  · have h0 : 0 ≤ q := le_of_not_gt hq
    obtain ⟨h1, h2⟩ := squash_num_den q h0
    have h3 : ¬ q / (1 + q) < 0 := not_lt.mpr (by positivity)
    simp only [hq, decide_false, Bool.false_eq_true, if_false, frameT_eq, value_eq_bitsValue,
      bitsValue_natBits, natBits_eq_bits, squash, ratBits, h1, h2, h3]

variable {Γ : Type} [Fintype Γ]

def testFn (est : ℕ → ℕ → ℕ → List (List Γ) → Bits → ℚ) (ρ r : MvPolynomial (Fin 3) ℕ)
    (q₀ : ℚ) (n : ℕ) (bl : List (List Γ)) (co : Bits) : ℚ :=
  if eval3 ρ n 2 2 ≤ bl.length then
    squash (est n (parA ρ n bl.length) (parA ρ n bl.length)
      (bl.take (eval3 ρ n (parA ρ n bl.length) (parA ρ n bl.length)))
      (co.take (eval3 r n (parA ρ n bl.length) (parA ρ n bl.length))))
  else squash q₀

def rT (r : MvPolynomial (Fin 3) ℕ) : MvPolynomial (Fin 2) ℕ :=
  MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1 + 2, MvPolynomial.X 1 + 2] r

theorem eval2_rT (r : MvPolynomial (Fin 3) ℕ) (n m : ℕ) :
    eval2 (rT r) n m = eval3 r n (m + 2) (m + 2) := by
  unfold eval2 eval3 rT
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp, MvPolynomial.bind₁_X_right, MvPolynomial.eval_X]
      congr 1
      fin_cases i <;> simp
theorem trace_of_outputs (M : Machine) {s t : List Bool} {n : ℕ}
    (h : TM2OutputsInTime M.tm s (some t) n) :
    ∃ k ≤ n, Trace M.step k (M.initialCfg s) (M.finalCfg t) :=
  ⟨h.steps, h.steps_le_m, Trace.of_iterate h.evals_in_steps⟩

theorem outputs_of_trace (M : Machine) {s t : List Bool} {n k : ℕ}
    (h : Trace M.step k (M.initialCfg s) (M.finalCfg t)) (hk : k ≤ n) :
    Nonempty (TM2OutputsInTime M.tm s (some t) n) :=
  ⟨⟨⟨k, h.iterate_eq⟩, hk⟩⟩

theorem assemble {pre post : Bits → Bits} (P : PolyProgram (id : Bits → Bits) id pre)
    (ME : Machine) (Q : PolyProgram (id : Bits → Bits) id post) {x y : Bits} {s₂ : ℕ}
    (hE : TM2OutputsInTime ME.tm (pre x) (some y) s₂) :
    Nonempty (TM2OutputsInTime (Compose.machine (Compose.machine P.machine ME) Q.machine).tm x
      (some (post y))
      (P.time.eval x.length + 2 * (pre x).length + 2 + s₂ + 2 * y.length + 2 +
        Q.time.eval y.length)) := by
  obtain ⟨k₁, hk₁, h₁⟩ := trace_of_outputs P.machine (P.outputs x)
  obtain ⟨k₂, hk₂, h₂⟩ := trace_of_outputs ME hE
  obtain ⟨k₃, hk₃, h₃⟩ := trace_of_outputs Q.machine (Q.outputs y)
  simp only [id_eq] at h₁ h₃ hk₁ hk₃
  have h12 := Compose.run P.machine ME h₁ h₂
  have h123 := Compose.run (Compose.machine P.machine ME) Q.machine h12 h₃
  refine outputs_of_trace _ h123 ?_
  omega

theorem mv_eval_mono {k : ℕ} (p : MvPolynomial (Fin k) ℕ) {x y : Fin k → ℕ}
    (h : ∀ i, x i ≤ y i) : MvPolynomial.eval x p ≤ MvPolynomial.eval y p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; omega
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact Nat.mul_le_mul hp (h i)

theorem eval3_mono (p : MvPolynomial (Fin 3) ℕ) {n a b n' a' b' : ℕ} (h1 : n ≤ n')
    (h2 : a ≤ a') (h3 : b ≤ b') : eval3 p n a b ≤ eval3 p n' a' b' :=
  mv_eval_mono p (by intro i; fin_cases i <;> simpa)

def univ {k : ℕ} (p : MvPolynomial (Fin k) ℕ) : Polynomial ℕ :=
  MvPolynomial.aeval (fun _ => Polynomial.X) p

theorem eval_univ {k : ℕ} (p : MvPolynomial (Fin k) ℕ) (N : ℕ) :
    (univ p).eval N = MvPolynomial.eval (fun _ => N) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [univ]
  | add p q hp hq => simp only [univ, map_add, Polynomial.eval_add] at *; rw [hp, hq]
  | mul_X p i hp =>
      simp only [univ, map_mul, Polynomial.eval_mul, MvPolynomial.aeval_X, Polynomial.eval_X,
        MvPolynomial.eval_X] at *
      rw [hp]

theorem eval3_le_univ (p : MvPolynomial (Fin 3) ℕ) {n a b N : ℕ} (h1 : n ≤ N) (h2 : a ≤ N)
    (h3 : b ≤ N) : eval3 p n a b ≤ (univ p).eval N := by
  rw [eval_univ]; exact mv_eval_mono p (by intro i; fin_cases i <;> simpa)

theorem ofFn_take_eq {α : Type} {m K : ℕ} (f : Fin m → α) (h : K ≤ m) :
    List.ofFn (fun i : Fin K => f ⟨i, lt_of_lt_of_le i.isLt h⟩) = (List.ofFn f).take K := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2; simp

theorem dbl_length (b : Bits) : (b.flatMap fun x => [x, x]).length = 2 * b.length := by
  induction b with
  | nil => simp
  | cons x b ih => simp [ih]; omega

theorem frame_length (l : List Bits) :
    (frame l).length = (l.map fun b => 2 * b.length + 2).sum := by
  induction l with
  | nil => simp [frame]
  | cons b bs ih => simp only [frame, List.length_append, dbl_length, ih]; simp

theorem stringBits_length (u : List Γ) : (stringBits u).length = u.length * Fintype.card Γ := by
  induction u with
  | nil => simp [stringBits]
  | cons a u ih =>
      simp only [stringBits, List.flatMap_cons, List.length_append] at ih ⊢
      rw [ih]; simp [symBits]; ring

theorem blockBits_length {m ℓ : ℕ} (xs : Fin m → Word Γ ℓ) :
    (blockBits (blockList xs)).length = m * (2 * (ℓ * Fintype.card Γ) + 2) := by
  rw [blockBits, frame_length, List.map_map]
  have : ∀ u ∈ blockList xs, ((fun b : Bits => 2 * b.length + 2) ∘ stringBits) u =
      2 * (ℓ * Fintype.card Γ) + 2 := by
    intro u hu
    simp only [blockList, List.mem_ofFn] at hu
    obtain ⟨i, rfl⟩ := hu
    simp [stringBits_length]
  rw [List.map_congr_left this]
  simp [blockList, Function.comp_def]

theorem input_length {m ℓ R : ℕ} (n : ℕ) (xs : Fin m → Word Γ ℓ) (ω : Fin R → Bool) :
    (frame [unary n, blockBits (blockList xs), coinBits ω]).length =
      (2 * n + 2) + (2 * (m * (2 * (ℓ * Fintype.card Γ) + 2)) + 2) + (2 * R + 2) := by
  rw [frame_length]; simp [unary, blockBits_length, coinBits]; omega

theorem pre_parts {n m ℓ R : ℕ} (xs : Fin m → Word Γ ℓ) (ω : Fin R → Bool) :
    comp 0 (frame [unary n, blockBits (blockList xs), coinBits ω]) = unary n ∧
    comp 1 (frame [unary n, blockBits (blockList xs), coinBits ω]) =
      frame ((blockList xs).map stringBits) ∧
    comp 2 (frame [unary n, blockBits (blockList xs), coinBits ω]) = coinBits ω ∧
    mOf (frame [unary n, blockBits (blockList xs), coinBits ω]) = m ∧
    padOf (frame [unary n, blockBits (blockList xs), coinBits ω]) = List.replicate (m + 3) true := by
  have hl : (blockList xs).length = m := by simp [blockList]
  refine ⟨comp_frame _ _, comp_frame _ _, comp_frame _ _, ?_, ?_⟩
  · simp only [mOf, comp_frame, List.getD_cons_succ, List.getD_cons_zero, blockBits, marks_frame,
      List.length_replicate, List.length_map, hl]
  · simp only [padOf, comp_frame, List.getD_cons_succ, List.getD_cons_zero, blockBits, marks_frame,
      List.length_map, hl, List.replicate_add]
    rfl

theorem AOf_eq (ρ : MvPolynomial (Fin 3) ℕ) {n m ℓ R : ℕ} (xs : Fin m → Word Γ ℓ)
    (ω : Fin R → Bool) :
    AOf ρ (frame [unary n, blockBits (blockList xs), coinBits ω]) = parA ρ n m := by
  obtain ⟨h0, -, -, hm, hp⟩ := pre_parts (n := n) xs ω
  unfold AOf parA
  rw [hm, hp, h0, findGreatest_eq_findIdx]
  simp [unary]

theorem pre_good (ρ r : MvPolynomial (Fin 3) ℕ) (z₀ : Bits) {n m ℓ R : ℕ}
    (xs : Fin m → Word Γ ℓ) (ω : Fin R → Bool) (hg : eval3 ρ n 2 2 ≤ m) :
    preFn ρ r z₀ (frame [unary n, blockBits (blockList xs), coinBits ω]) =
      frame [unary n, unary (parA ρ n m), unary (parA ρ n m),
        blockBits ((blockList xs).take (eval3 ρ n (parA ρ n m) (parA ρ n m))),
        (coinBits ω).take (eval3 r n (parA ρ n m) (parA ρ n m))] := by
  obtain ⟨h0, h1, h2, hm, hp⟩ := pre_parts (n := n) xs ω
  have hA := AOf_eq ρ (n := n) xs ω
  have hAm : parA ρ n m ≤ m + 2 := Nat.findGreatest_le _
  have hn : (unary n).length = n := by simp [unary]
  unfold preFn
  rw [h0, hm, hn, if_pos hg, hA, hp, h1, h2, takeComps_frame, frameT_eq, List.take_replicate,
    Nat.min_eq_left (by omega), blockBits, List.map_take]
  rfl

theorem pre_bad (ρ r : MvPolynomial (Fin 3) ℕ) (z₀ : Bits) {n m ℓ R : ℕ}
    (xs : Fin m → Word Γ ℓ) (ω : Fin R → Bool) (hg : ¬ eval3 ρ n 2 2 ≤ m) :
    preFn ρ r z₀ (frame [unary n, blockBits (blockList xs), coinBits ω]) = z₀ := by
  obtain ⟨h0, h1, h2, hm, hp⟩ := pre_parts (n := n) xs ω
  have hn : (unary n).length = n := by simp [unary]
  unfold preFn
  rw [h0, hm, hn, if_neg hg]

theorem parA_spec (ρ : MvPolynomial (Fin 3) ℕ) {n m : ℕ} (hg : eval3 ρ n 2 2 ≤ m) :
    2 ≤ parA ρ n m ∧ parA ρ n m ≤ m + 2 ∧
      eval3 ρ n (parA ρ n m) (parA ρ n m) ≤ m := by
  refine ⟨Nat.le_findGreatest (by omega) hg, Nat.findGreatest_le _,
    Nat.findGreatest_spec (P := fun j => eval3 ρ n j j ≤ m) (by omega) hg⟩

def progOf (M : Machine) : Program := ⟨M.tm, Equiv.refl _, Equiv.refl _⟩

theorem progOf_outputs (M : Machine) {x y : Bits} {t : ℕ}
    (h : Nonempty (TM2OutputsInTime M.tm x (some y) t)) : (progOf M).OutputsWithin x y t := by
  have e0 : ∀ l : Bits, l.map (progOf M).inAlph.symm = l := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => exact congrArg (List.cons a) ih
  have e1 : ∀ l : Bits, l.map (progOf M).outAlph.symm = l := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => exact congrArg (List.cons a) ih
  unfold Program.OutputsWithin
  rw [e0 x, e1 y]
  exact h

theorem tester_runs (𝒞 : DistributionClass Γ) (E : Program) (time : Polynomial ℕ)
    (ρ r : MvPolynomial (Fin 3) ℕ) (est : ℕ → ℕ → ℕ → List (List Γ) → Bits → ℚ)
    (hrun : ∀ n, ∀ D ∈ 𝒞.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      ∀ (xs : Fin (eval3 ρ n a b) → Word Γ D.length) (ω : Fin (eval3 r n a b) → Bool),
        E.OutputsWithin
          (frame [unary n, unary a, unary b, blockBits (blockList xs), coinBits ω])
          (ratBits (est n a b (blockList xs) (coinBits ω))) (time.eval (n + a + b)))
    (n₀ : ℕ) (D₀ : Source Γ) (hD₀ : D₀ ∈ 𝒞.members n₀) (w₀ : Word Γ D₀.length) :
    ∃ (T : Program) (timeT : Polynomial ℕ), ∀ n, ∀ D ∈ 𝒞.members n, ∀ (m : ℕ)
      (xs : Fin m → Word Γ D.length) (ω : Fin (eval2 (rT r) n m) → Bool),
      T.OutputsWithin (frame [unary n, blockBits (blockList xs), coinBits ω])
        (ratBits (testFn est ρ r
          (est n₀ 2 2 (blockList (fun _ : Fin (eval3 ρ n₀ 2 2) => w₀))
            (coinBits (fun _ : Fin (eval3 r n₀ 2 2) => false)))
          n (blockList xs) (coinBits ω))) (timeT.eval (n + m)) := by
  obtain ⟨ME, τ, hME⟩ := QMCBoolSim.simulate E.tm E.inAlph E.outAlph
  set q₀ := est n₀ 2 2 (blockList (fun _ : Fin (eval3 ρ n₀ 2 2) => w₀))
      (coinBits (fun _ : Fin (eval3 r n₀ 2 2) => false)) with hq₀
  set z₀ := frame [unary n₀, unary 2, unary 2,
    blockBits (blockList (fun _ : Fin (eval3 ρ n₀ 2 2) => w₀)),
    coinBits (fun _ : Fin (eval3 r n₀ 2 2) => false)] with hz₀
  obtain ⟨P⟩ := pre_poly ρ r z₀
  obtain ⟨Q⟩ := post_poly τ
  let M := Compose.machine (Compose.machine P.machine ME) Q.machine
  let X : Polynomial ℕ := Polynomial.X
  let Lx : Polynomial ℕ := Polynomial.C 6 + Polynomial.C 2 * X +
    Polynomial.C 2 * (X * (Polynomial.C 2 * (X * Polynomial.C (Fintype.card Γ)) + Polynomial.C 2)) +
    Polynomial.C 2 * (univ r).comp (X + Polynomial.C 2)
  let Le : Polynomial ℕ := P.sizeBound.comp Lx
  let Ts : Polynomial ℕ := time.comp (Polynomial.C 2 * X + Polynomial.C 4) +
    Polynomial.C (time.eval (n₀ + 2 + 2))
  let Ly : Polynomial ℕ := Le + Ts * Polynomial.C ME.growth
  refine ⟨progOf M,
    P.time.comp Lx + Polynomial.C 2 * Le + Polynomial.C 2 + Ts + Polynomial.C 2 * Ly +
      Polynomial.C 2 + Q.time.comp Ly, ?_⟩
  intro n D hD m xs ω
  set x := frame [unary n, blockBits (blockList xs), coinBits ω] with hx
  -- the estimator run
  have key : ∃ (v : ℚ) (s₂ : ℕ), s₂ ≤ Ts.eval (n + m) ∧
      Nonempty (TM2OutputsInTime ME.tm (preFn ρ r z₀ x) (some (((ratBits v).map τ : Bits))) s₂) ∧
      testFn est ρ r q₀ n (blockList xs) (coinBits ω) = squash v := by
    by_cases hg : eval3 ρ n 2 2 ≤ m
    · obtain ⟨hA2, hAm, hK⟩ := parA_spec ρ hg
      set A := parA ρ n m with hA
      have hR : eval3 r n A A ≤ eval2 (rT r) n m := by
        rw [eval2_rT]; exact eval3_mono r le_rfl (by omega) (by omega)
      let xs' : Fin (eval3 ρ n A A) → Word Γ D.length := fun i => xs ⟨i, by omega⟩
      let ω' : Fin (eval3 r n A A) → Bool := fun i => ω ⟨i, by omega⟩
      have hbl : blockList xs' = (blockList xs).take (eval3 ρ n A A) :=
        ofFn_take_eq (fun i => List.ofFn (xs i)) hK
      have hco : coinBits ω' = (coinBits ω).take (eval3 r n A A) := ofFn_take_eq ω hR
      refine ⟨est n A A (blockList xs') (coinBits ω'), time.eval (n + A + A), ?_, ?_, ?_⟩
      · simp only [Ts, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X, X]
        have := polynomial_eval_mono time (show n + A + A ≤ 2 * (n + m) + 4 by omega)
        omega
      · obtain ⟨h⟩ := hrun n D hD A A hA2 hA2 xs' ω'
        have := hME _ _ _ h
        rw [hx, pre_good ρ r z₀ xs ω hg, ← hbl, ← hco]
        exact this
      · have hl : (blockList xs).length = m := by simp [blockList]
        simp only [testFn, hl, if_pos hg, ← hA, hbl, hco]
    · refine ⟨q₀, time.eval (n₀ + 2 + 2), ?_, ?_, ?_⟩
      · simp only [Ts, Polynomial.eval_add, Polynomial.eval_C]; omega
      · obtain ⟨h⟩ := hrun n₀ D₀ hD₀ 2 2 le_rfl le_rfl (fun _ => w₀) (fun _ => false)
        have := hME _ _ _ h
        rw [hx, pre_bad ρ r z₀ xs ω hg]
        exact this
      · have hl : (blockList xs).length = m := by simp [blockList]
        simp only [testFn, hl, if_neg hg]
  obtain ⟨v, s₂, hs₂, ⟨hE⟩, hv⟩ := key
  obtain ⟨hT⟩ := assemble P ME Q hE
  rw [post_correct] at hT
  -- length bounds
  have hxl : x.length ≤ Lx.eval (n + m) := by
    rw [hx, input_length]
    have hl := 𝒞.length_le n D hD
    have hr : eval2 (rT r) n m ≤ (univ r).eval (n + m + 2) := by
      rw [eval2_rT]; exact eval3_le_univ r (by omega) (by omega) (by omega)
    simp only [Lx, X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp]
    have h1 : m * (2 * (D.length * Fintype.card Γ) + 2) ≤
        (n + m) * (2 * ((n + m) * Fintype.card Γ) + 2) :=
      Nat.mul_le_mul (by omega) (by gcongr; omega)
    omega
  have hel : (preFn ρ r z₀ x).length ≤ Le.eval (n + m) := by
    have := P.length_bound x
    simp only [id_eq] at this
    simp only [Le, Polynomial.eval_comp]
    exact this.trans (polynomial_eval_mono _ hxl)
  have hyl : ((ratBits v).map τ).length ≤ Ly.eval (n + m) := by
    have := ME.output_length hE
    simp only [Ly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    have := Nat.mul_le_mul_right ME.growth hs₂
    omega
  have hPt := polynomial_eval_mono P.time hxl
  have hQt := polynomial_eval_mono Q.time hyl
  apply progOf_outputs
  rw [hv]
  refine ⟨⟨hT.toEvalsTo, le_trans hT.steps_le_m ?_⟩⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  omega



def restr {α : Type} {K m : ℕ} (h : K ≤ m) (xs : Fin m → α) : Fin K → α :=
  fun i => xs (Fin.castLE h i)

theorem pmf_eq_of_subsingleton {α : Type} [Subsingleton α] (p q : PMF α) : p = q := by
  ext x
  have hp : p x = 1 := by
    have h := p.tsum_coe
    rwa [tsum_eq_single x (fun y hy => absurd (Subsingleton.elim y x) hy)] at h
  have hq : q x = 1 := by
    have h := q.tsum_coe
    rwa [tsum_eq_single x (fun y hy => absurd (Subsingleton.elim y x) hy)] at h
  rw [hp, hq]

theorem iid_map_restr {Ω : Type} (P : PMF Ω) :
    ∀ (K m : ℕ) (h : K ≤ m), (iid P m).map (restr h) = iid P K := by
  intro K
  induction K with
  | zero => intro m h; exact pmf_eq_of_subsingleton _ _
  | succ K ih =>
      intro m h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h' : K ≤ m' := by omega
      simp only [iid, PMF.map_bind, PMF.map_comp]
      congr 1
      funext x
      rw [← ih m' h', PMF.map_comp]
      congr 1
      funext ys i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp only [Function.comp, restr]
        rw [Fin.cons_succ]
        have : Fin.castLE h j.succ = (Fin.castLE h' j).succ := Fin.ext (by simp)
        rw [this, Fin.cons_succ]
        rfl

theorem iid_apply {Ω : Type} (P : PMF Ω) : ∀ (m : ℕ) (xs : Fin m → Ω),
    iid P m xs = ∏ i, P (xs i) := by
  intro m
  induction m with
  | zero =>
      intro xs
      simp only [iid, PMF.pure_apply, Finset.univ_eq_empty, Finset.prod_empty]
      rw [if_pos (Subsingleton.elim _ _)]
  | succ m ih =>
      intro xs
      simp only [iid, PMF.bind_apply, PMF.map_apply]
      rw [tsum_eq_single (xs 0)]
      · rw [tsum_eq_single (Fin.tail xs)]
        · rw [if_pos (Fin.cons_self_tail xs).symm, ih, Fin.prod_univ_succ]
          rfl
        · intro y hy
          rw [if_neg]
          intro hxy
          apply hy
          rw [hxy]; rfl
      · intro a ha
        rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
        intro y
        rw [if_neg]
        intro hxy
        apply ha
        rw [hxy]; rfl

theorem coinLaw_eq_iid (r : ℕ) : coinLaw r = iid (PMF.uniformOfFintype Bool) r := by
  ext ω
  rw [iid_apply, coinLaw]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ]
  push_cast
  rw [ENNReal.inv_pow]

theorem coinLaw_map_restr {K m : ℕ} (h : K ≤ m) : (coinLaw m).map (restr h) = coinLaw K := by
  rw [coinLaw_eq_iid, coinLaw_eq_iid, iid_map_restr]

theorem samplesAndCoins_map {Ω : Type} (P : PMF Ω) {K m R R' : ℕ} (hK : K ≤ m) (hR : R ≤ R') :
    (samplesAndCoins P m R').map (fun p => (restr hK p.1, restr hR p.2)) =
      samplesAndCoins P K R := by
  simp only [samplesAndCoins, PMF.map_bind, PMF.map_comp]
  have : ∀ xs : Fin m → Ω, ((fun p : (Fin K → Ω) × (Fin R → Bool) => p) ∘
      (fun p : (Fin m → Ω) × (Fin R' → Bool) => (restr hK p.1, restr hR p.2)) ∘
        fun ω => (xs, ω)) = (fun ω => (restr hK xs, ω)) ∘ restr hR := by
    intro xs; rfl
  conv_lhs => arg 2; ext xs; rw [show ((fun p : (Fin m → Ω) × (Fin R' → Bool) =>
    (restr hK p.1, restr hR p.2)) ∘ fun ω => (xs, ω)) = (fun ω => (restr hK xs, ω)) ∘ restr hR
    from rfl, ← PMF.map_comp, coinLaw_map_restr]
  rw [show (fun xs : Fin m → Ω => (coinLaw R).map (fun ω => (restr hK xs, ω))) =
    (fun ys => (coinLaw R).map (fun ω => (ys, ω))) ∘ restr hK from rfl, ← PMF.bind_map,
    iid_map_restr]

theorem mass_map {α β : Type} [Fintype α] (p : PMF α) (g : α → β) (y : β) :
    mass (p.map g) y = ∑ x, if y = g x then mass p x else 0 := by
  rw [mass, PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · congr 1; funext x; split_ifs <;> simp [mass]
  · intro x _; split_ifs
    · exact PMF.apply_ne_top p x
    · exact ENNReal.zero_ne_top

theorem expectation_map {α β : Type} [Fintype α] [Fintype β] (p : PMF α) (g : α → β)
    (f : β → ℝ) : expectation (p.map g) f = expectation p (fun x => f (g x)) := by
  unfold expectation
  simp only [mass_map, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; funext x
  simp [ite_mul]

theorem sum_mass {α : Type} [Fintype α] (p : PMF α) : ∑ x, mass p x = 1 := by
  unfold mass
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top p x)]
  have := p.tsum_coe
  rw [tsum_fintype] at this
  rw [this]; simp

theorem mass_nonneg {α : Type} (p : PMF α) (x : α) : 0 ≤ mass p x := ENNReal.toReal_nonneg

theorem expectation_mono {α : Type} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : expectation p f ≤ expectation p g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (mass_nonneg p x)

theorem expectation_upper {α : Type} [Fintype α] (p : PMF α) (f : α → ℝ) (A : α → Prop)
    (u : ℝ) (hu : 0 ≤ u) (h1 : ∀ x, f x ≤ 1) (hA : ∀ x, A x → f x ≤ u) :
    expectation p f ≤ u + (1 - eventProbability p A) := by
  have key : expectation p f ≤ expectation p (fun x => u + (1 - if A x then 1 else 0)) :=
    expectation_mono p fun x => by
      by_cases hx : A x
      · simp [hx, hA x hx]
      · simp [hx]; linarith [h1 x]
  refine key.trans (le_of_eq ?_)
  unfold eventProbability expectation
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_mass, mul_one]
  ring

theorem expectation_lower {α : Type} [Fintype α] (p : PMF α) (f : α → ℝ) (A : α → Prop)
    (l : ℝ) (hl : 0 ≤ l) (h0 : ∀ x, 0 ≤ f x) (hA : ∀ x, A x → l ≤ f x) :
    l * eventProbability p A ≤ expectation p f := by
  have key : expectation p (fun x => l * if A x then 1 else 0) ≤ expectation p f :=
    expectation_mono p fun x => by
      by_cases hx : A x
      · simp [hx, hA x hx]
      · simp [hx, h0 x]
  refine le_trans (le_of_eq ?_) key
  unfold eventProbability expectation
  rw [Finset.mul_sum]; congr 1; funext x; ring

theorem eventProbability_le_one {α : Type} [Fintype α] (p : PMF α) (A : α → Prop) :
    eventProbability p A ≤ 1 := by
  have := expectation_mono p (f := fun x => if A x then (1:ℝ) else 0) (g := fun _ => 1)
    (fun x => by split_ifs <;> norm_num)
  unfold eventProbability
  refine this.trans (le_of_eq ?_)
  unfold expectation; simp [sum_mass]

theorem entropy_nonneg {α : Type} [Fintype α] (p : PMF α) : 0 ≤ entropy p := by
  unfold entropy FuchsVdGraaf.entropy
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro x _
  have h0 := mass_nonneg p x
  have h1 : mass p x ≤ 1 := by
    have := Finset.single_le_sum (f := mass p) (fun y _ => mass_nonneg p y) (Finset.mem_univ x)
    rw [sum_mass] at this; exact this
  exact mul_nonpos_of_nonneg_of_nonpos h0 (Real.logb_nonpos (by norm_num) h0 h1)

theorem entropy_le_logb_card {α : Type} [Fintype α] [Nonempty α] (p : PMF α) :
    entropy p ≤ Real.logb 2 (Fintype.card α) := by
  unfold entropy FuchsVdGraaf.entropy
  set N : ℝ := (Fintype.card α : ℝ)
  have hN : 0 < N := by simp [N, Fintype.card_pos]
  have key : ∀ x, -(mass p x * Real.log (mass p x)) - mass p x * Real.log N ≤ 1 / N - mass p x := by
    intro x
    have h0 := mass_nonneg p x
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp; positivity
    · have hl := Real.log_le_sub_one_of_pos (show 0 < 1 / (N * mass p x) by positivity)
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul hN.ne' h.ne'] at hl
      have : mass p x * (1 / (N * mass p x) - 1) = 1 / N - mass p x := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hl h0]
  have hs : ∑ x, (-(mass p x * Real.log (mass p x)) - mass p x * Real.log N) ≤ 0 := by
    calc _ ≤ ∑ x : α, (1 / N - mass p x) := Finset.sum_le_sum fun x _ => key x
      _ = 0 := by rw [Finset.sum_sub_distrib, sum_mass]; simp [N]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_mass, one_mul] at hs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb]
  have : -∑ x, mass p x * (Real.log (mass p x) / Real.log 2) =
      (∑ x, -(mass p x * Real.log (mass p x))) / Real.log 2 := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]; congr 1; funext x; ring
  rw [this, div_le_div_iff_of_pos_right hlog2]
  linarith



def φR (t : ℝ) : ℝ := if t < 0 then 0 else t / (1 + t)

theorem φR_nonneg (t : ℝ) : 0 ≤ φR t := by
  unfold φR; split_ifs with h
  · exact le_rfl
  · push_neg at h; positivity

theorem φR_le_one (t : ℝ) : φR t ≤ 1 := by
  unfold φR; split_ifs with h
  · norm_num
  · push_neg at h; rw [div_le_one (by linarith)]; linarith

theorem φR_mono {s t : ℝ} (h : s ≤ t) : φR s ≤ φR t := by
  unfold φR
  split_ifs with h1 h2 h2
  · exact le_rfl
  · push_neg at h2; positivity
  · linarith
  · push_neg at h1 h2
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem φR_gap {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (y - x) / (1 + y) ^ 2 ≤ φR y - φR x := by
  have hy : 0 ≤ y := hx.trans hxy
  unfold φR
  rw [if_neg (not_lt.mpr hx), if_neg (not_lt.mpr hy)]
  have e : y / (1 + y) - x / (1 + x) = (y - x) / ((1 + x) * (1 + y)) := by
    field_simp; ring
  rw [e]
  apply div_le_div_of_nonneg_left (by linarith) (by positivity)
  rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)

theorem final_ineq {u L ε x y : ℝ} (hL : 2 ≤ L) (hu : 8 * L ^ 2 ≤ u) (hε0 : 0 ≤ ε)
    (hε : ε * u ^ 4 ≤ 2) (hx : 0 ≤ x) (hyx : u⁻¹ - 2 * ε ≤ y - x) (hy : 1 + y ≤ L) :
    (u⁻¹) ^ 2 ≤ φR y * (1 - ε) - (φR x + ε) := by
  have hu0 : 0 < u := by nlinarith
  set v := u⁻¹ with hv
  have hv0 : 0 < v := inv_pos.mpr hu0
  have huv : u * v = 1 := mul_inv_cancel₀ hu0.ne'
  have hLv : L ^ 2 * v ≤ 1 / 8 := by
    rw [le_div_iff₀ (by norm_num)]
    calc L ^ 2 * v * 8 = (8 * L ^ 2) * v := by ring
      _ ≤ u * v := mul_le_mul_of_nonneg_right hu hv0.le
      _ = 1 := huv
  have hv32 : v ≤ 1 / 32 := by nlinarith
  have hεv : ε ≤ 2 * v ^ 4 := by
    have : ε = ε * u ^ 4 * v ^ 4 := by
      rw [mul_assoc, ← mul_pow, huv, one_pow, mul_one]
    rw [this]; exact mul_le_mul_of_nonneg_right hε (by positivity)
  have hv3 : v ^ 3 ≤ 1 / 16 := by
    have := pow_le_pow_left₀ hv0.le hv32 3
    norm_num at this ⊢; linarith
  have hv4 : v ^ 4 ≤ v / 16 := by
    have := mul_le_mul_of_nonneg_left hv3 hv0.le
    nlinarith
  have h2ε : 2 * ε ≤ v / 4 := by nlinarith
  have hyx' : x ≤ y := by linarith
  have hgap := φR_gap hx hyx'
  have hL2 : (1 + y) ^ 2 ≤ L ^ 2 := by
    have : 0 ≤ 1 + y := by linarith
    nlinarith
  have hq : (y - x) / L ^ 2 ≤ (y - x) / (1 + y) ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (by nlinarith) hL2
  have h1 := φR_le_one y
  have h0 := φR_nonneg y
  -- φR y (1-ε) - φR x - ε ≥ (y - x)/L² - 2ε ≥ (v - 2ε)/L² - 2ε
  have hmain : v ^ 2 + 2 * ε ≤ (v - 2 * ε) / L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hv3' : 2 * ε * (L ^ 2 + 1) ≤ v / 2 := by
      have e1 : ε * L ^ 2 ≤ 2 * v ^ 4 * L ^ 2 :=
        mul_le_mul_of_nonneg_right hεv (by positivity)
      have e2 : 2 * v ^ 4 * L ^ 2 = 2 * v ^ 3 * (L ^ 2 * v) := by ring
      have e3 : 2 * v ^ 3 * (L ^ 2 * v) ≤ 2 * v ^ 3 * (1 / 8) :=
        mul_le_mul_of_nonneg_left hLv (by positivity)
      have v2 : v ^ 2 ≤ 1 / 16 := by nlinarith
      have e4 : v ^ 3 ≤ v / 16 := by
        calc v ^ 3 = v * v ^ 2 := by ring
          _ ≤ v * (1 / 16) := mul_le_mul_of_nonneg_left v2 hv0.le
          _ = v / 16 := by ring
      nlinarith
    have hv2 : v ^ 2 * L ^ 2 ≤ v / 8 := by nlinarith
    nlinarith
  have hfin : (v - 2 * ε) / L ^ 2 ≤ (y - x) / L ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  nlinarith

theorem poly_le_pow (p : Polynomial ℕ) : ∃ k, 1 ≤ k ∧ ∀ N, 2 ≤ N → p.eval N ≤ N ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨k₁, hk₁, h₁⟩ := hp
      obtain ⟨k₂, hk₂, h₂⟩ := hq
      refine ⟨max k₁ k₂ + 1, by omega, fun N hN => ?_⟩
      rw [Polynomial.eval_add, pow_succ]
      have e1 : N ^ k₁ ≤ N ^ max k₁ k₂ := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have e2 : N ^ k₂ ≤ N ^ max k₁ k₂ := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have := h₁ N hN
      have := h₂ N hN
      nlinarith
  | monomial e a =>
      refine ⟨a + e + 1, by omega, fun N hN => ?_⟩
      rw [Polynomial.eval_monomial]
      have ha : a ≤ N ^ a := (Nat.lt_pow_self (by omega : 1 < N)).le
      calc a * N ^ e ≤ N ^ a * N ^ e := Nat.mul_le_mul_right _ ha
        _ = N ^ (a + e) := (pow_add _ _ _).symm
        _ ≤ N ^ (a + e + 1) := Nat.pow_le_pow_right (by omega) (by omega)

theorem squash_cast (q : ℚ) : ((squash q : ℚ) : ℝ) = φR (q : ℝ) := by
  unfold squash φR
  by_cases h : q < 0
  · have h' : (q : ℝ) < 0 := by exact_mod_cast h
    simp [h, h']
  · have h' : ¬ (q : ℝ) < 0 := by exact_mod_cast h
    simp [h, h']

theorem exp_testFn (est : ℕ → ℕ → ℕ → List (List Γ) → Bits → ℚ) (ρ r : MvPolynomial (Fin 3) ℕ)
    (q₀ : ℚ) {n m ℓ : ℕ} (P : PMF (Word Γ ℓ)) (hg : eval3 ρ n 2 2 ≤ m)
    (hK : eval3 ρ n (parA ρ n m) (parA ρ n m) ≤ m)
    (hR : eval3 r n (parA ρ n m) (parA ρ n m) ≤ eval2 (rT r) n m) :
    expectation (samplesAndCoins P m (eval2 (rT r) n m))
        (fun p => ((testFn est ρ r q₀ n (blockList p.1) (coinBits p.2) : ℚ) : ℝ)) =
      expectation (samplesAndCoins P (eval3 ρ n (parA ρ n m) (parA ρ n m))
          (eval3 r n (parA ρ n m) (parA ρ n m)))
        (fun p => φR ((est n (parA ρ n m) (parA ρ n m) (blockList p.1) (coinBits p.2) : ℚ) : ℝ)) := by
  rw [← samplesAndCoins_map P hK hR, expectation_map]
  congr 1; funext p
  have hl : (blockList p.1).length = m := by simp [blockList]
  simp only [testFn, hl, if_pos hg]
  rw [squash_cast]
  have h1 : blockList (restr hK p.1) = (blockList p.1).take (eval3 ρ n (parA ρ n m) (parA ρ n m)) :=
    ofFn_take_eq (fun i => List.ofFn (p.1 i)) hK
  have h2 : coinBits (restr hR p.2) = (coinBits p.2).take (eval3 r n (parA ρ n m) (parA ρ n m)) :=
    ofFn_take_eq p.2 hR
  rw [h1, h2]

theorem tester_gap (hΓ : 1 ≤ Fintype.card Γ) (𝒞 : DistributionClass Γ) (ρ r : MvPolynomial (Fin 3) ℕ)
    (est : ℕ → ℕ → ℕ → List (List Γ) → Bits → ℚ)
    (hcomp : ∀ n, ∀ D ∈ 𝒞.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      1 - 1 / (b : ℝ) ≤ eventProbability (samplesAndCoins D.law (eval3 ρ n a b) (eval3 r n a b))
        (fun p => ((est n a b (blockList p.1) (coinBits p.2) : ℚ) : ℝ) ≤
          entropy D.law + 1 / (a : ℝ)))
    (hsound : ∀ n, ∀ D ∈ 𝒞.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      ∀ Q : PMF (Word Γ D.length),
      1 - 1 / (b : ℝ) ≤ eventProbability (samplesAndCoins Q (eval3 ρ n a b) (eval3 r n a b))
        (fun p => entropy Q - 1 / (a : ℝ) ≤
          ((est n a b (blockList p.1) (coinBits p.2) : ℚ) : ℝ))) (q₀ : ℚ) :
    ∃ (ρT : Polynomial ℕ) (a b : ℝ), 0 < a ∧ 0 < b ∧
    (∀ n, ∀ D ∈ 𝒞.members n, ∀ m : ℕ, ρT.eval n ≤ m →
      ∀ Q : PMF (Word Γ D.length), entropy D.law + (m : ℝ) ^ (-a) ≤ entropy Q →
        (m : ℝ) ^ (-b) ≤
          expectation (samplesAndCoins Q m (eval2 (rT r) n m))
              (fun p => ((testFn est ρ r q₀ n (blockList p.1) (coinBits p.2) : ℚ) : ℝ)) -
            expectation (samplesAndCoins D.law m (eval2 (rT r) n m))
              (fun p => ((testFn est ρ r q₀ n (blockList p.1) (coinBits p.2) : ℚ) : ℝ))) := by
  obtain ⟨k, hk1, hk⟩ := poly_le_pow (univ ρ)
  have hk0 : (4 * k : ℕ) ≠ 0 := by omega
  refine ⟨(Polynomial.C 8 * (Polynomial.C (Fintype.card Γ) * Polynomial.X + Polynomial.C 2) ^ 2)
      ^ (4 * k) + (univ ρ).comp (Polynomial.X + Polynomial.C 2),
    ((4 * k : ℕ) : ℝ)⁻¹, ((4 * k : ℕ) : ℝ)⁻¹ * 2, by positivity, by positivity, ?_⟩
  intro n D hD m hm Q hQ
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_comp] at hm
  have hg : eval3 ρ n 2 2 ≤ m :=
    (eval3_le_univ ρ (N := n + 2) (by omega) (by omega) (by omega)).trans (by omega)
  obtain ⟨hA2, hAm, hK⟩ := parA_spec ρ hg
  have hR : eval3 r n (parA ρ n m) (parA ρ n m) ≤ eval2 (rT r) n m := by
    rw [eval2_rT]; exact eval3_mono r le_rfl (by omega) (by omega)
  rw [exp_testFn est ρ r q₀ Q hg hK hR, exp_testFn est ρ r q₀ D.law hg hK hR]
  have hs := hsound n D hD _ _ hA2 hA2 Q
  have hcp := hcomp n D hD _ _ hA2 hA2
  set A := parA ρ n m with hA
  set c := Fintype.card Γ with hc
  have hm0 : (8 * (c * n + 2) ^ 2) ^ (4 * k) ≤ m := by omega
  set L : ℝ := (c : ℝ) * n + 2 with hL
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hΓ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL2 : 2 ≤ L := by nlinarith
  have hLn : (n : ℝ) + 2 ≤ L := by nlinarith
  have hm0r : (8 * L ^ 2) ^ (4 * k) ≤ (m : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hm0
    push_cast at this
    simpa [hL] using this
  set u : ℝ := (m : ℝ) ^ (((4 * k : ℕ) : ℝ)⁻¹) with hu
  have hu8 : 8 * L ^ 2 ≤ u := by
    have h := Real.rpow_le_rpow (by positivity) hm0r
      (by positivity : (0:ℝ) ≤ ((4 * k : ℕ) : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (by positivity) hk0] at h
  have hum : u ^ (4 * k) = m := Real.rpow_inv_natCast_pow (Nat.cast_nonneg m) hk0
  have hu1 : 1 ≤ u := by nlinarith
  have hu4 : u ≤ u ^ 4 := le_self_pow₀ hu1 (by norm_num)
  have hbig : 2 * (n : ℝ) + 4 ≤ u ^ 4 := by nlinarith
  set F := ⌊u ^ 4⌋₊ with hF
  have hF1 : (F : ℝ) ≤ u ^ 4 := Nat.floor_le (by positivity)
  have hF2 : u ^ 4 < F + 1 := Nat.lt_floor_add_one _
  have hFn : n + 2 ≤ F := by
    apply Nat.le_floor; push_cast; linarith
  have hFk : F ^ k ≤ m := by
    have h : (F : ℝ) ^ k ≤ (u ^ 4) ^ k := pow_le_pow_left₀ (by positivity) hF1 k
    rw [← pow_mul, hum] at h
    exact_mod_cast h
  have hjgood : eval3 ρ n (F - n) (F - n) ≤ m :=
    (eval3_le_univ ρ (N := F) (by omega) (by omega) (by omega)).trans
      ((hk F (by omega)).trans hFk)
  have hjm : F - n ≤ m + 2 := by
    have : F ≤ F ^ k := Nat.le_self_pow (by omega) F
    omega
  have hjA : F - n ≤ A := Nat.le_findGreatest hjm hjgood
  have hAr : u ^ 4 / 2 ≤ (A : ℝ) := by
    have e1 : ((F - n : ℕ) : ℝ) = F - n := by rw [Nat.cast_sub (by omega)]
    have e2 : ((F - n : ℕ) : ℝ) ≤ A := by exact_mod_cast hjA
    linarith
  have hA0 : (0 : ℝ) < A := Nat.cast_pos.mpr (by omega)
  have hε0 : (0 : ℝ) ≤ 1 / (A : ℝ) := by positivity
  have hεu : 1 / (A : ℝ) * u ^ 4 ≤ 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hA0]; linarith
  have hHD := entropy_nonneg D.law
  haveI : Nonempty (Word Γ D.length) := ⟨Q.support_nonempty.some⟩
  have hHQ : entropy Q ≤ (c : ℝ) * n := by
    have h := entropy_le_logb_card Q
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.logb_pow] at h
    have hl : (D.length : ℝ) ≤ n := by exact_mod_cast 𝒞.length_le n D hD
    have hlc : Real.logb 2 (c : ℝ) ≤ c := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
      exact_mod_cast (Nat.lt_two_pow_self).le
    have hlc0 : 0 ≤ Real.logb 2 (c : ℝ) := Real.logb_nonneg (by norm_num) hc1
    calc entropy Q ≤ D.length * Real.logb 2 c := h
      _ ≤ n * c := mul_le_mul hl hlc hlc0 hn0
      _ = c * n := by ring
  have hEQ := expectation_lower (samplesAndCoins Q (eval3 ρ n A A) (eval3 r n A A))
    (fun p => φR ((est n A A (blockList p.1) (coinBits p.2) : ℚ) : ℝ))
    (fun p => entropy Q - 1 / (A : ℝ) ≤ ((est n A A (blockList p.1) (coinBits p.2) : ℚ) : ℝ))
    (φR (entropy Q - 1 / (A : ℝ)))
    (φR_nonneg _) (fun p => φR_nonneg _) (fun p hp => φR_mono hp)
  have hED := expectation_upper (samplesAndCoins D.law (eval3 ρ n A A) (eval3 r n A A))
    (fun p => φR ((est n A A (blockList p.1) (coinBits p.2) : ℚ) : ℝ))
    (fun p => ((est n A A (blockList p.1) (coinBits p.2) : ℚ) : ℝ) ≤ entropy D.law + 1 / (A : ℝ))
    (φR (entropy D.law + 1 / (A : ℝ)))
    (φR_nonneg _) (fun p => φR_le_one _) (fun p hp => φR_mono hp)
  have hEQ' : φR (entropy Q - 1 / (A : ℝ)) * (1 - 1 / (A : ℝ)) ≤
      φR (entropy Q - 1 / (A : ℝ)) * eventProbability (samplesAndCoins Q
        (eval3 ρ n A A) (eval3 r n A A))
        (fun p => entropy Q - 1 / (A : ℝ) ≤ ((est n A A (blockList p.1) (coinBits p.2) : ℚ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hs (φR_nonneg _)
  have hma : (m : ℝ) ^ (-((4 * k : ℕ) : ℝ)⁻¹) = u⁻¹ := Real.rpow_neg (Nat.cast_nonneg _) _
  have hmb : (m : ℝ) ^ (-(((4 * k : ℕ) : ℝ)⁻¹ * 2)) = (u⁻¹) ^ 2 := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_mul (Nat.cast_nonneg _), ← hu,
      inv_pow]
    norm_cast
  rw [hma] at hQ
  rw [hmb]
  have hfin := final_ineq (u := u) (L := L) (ε := 1 / (A : ℝ))
    (x := entropy D.law + 1 / (A : ℝ)) (y := entropy Q - 1 / (A : ℝ)) hL2 hu8 hε0 hεu
    (by positivity) (by linarith) (by linarith)
  linarith

theorem testFn_mem (est : ℕ → ℕ → ℕ → List (List Γ) → Bits → ℚ) (ρ r : MvPolynomial (Fin 3) ℕ)
    (q₀ : ℚ) (n : ℕ) (bl : List (List Γ)) (co : Bits) :
    0 ≤ testFn est ρ r q₀ n bl co ∧ testFn est ρ r q₀ n bl co ≤ 1 := by
  unfold testFn; split_ifs
  · exact ⟨squash_nonneg _, squash_le_one _⟩
  · exact ⟨squash_nonneg _, squash_le_one _⟩

theorem main (hΓ : 1 ≤ Fintype.card Γ) (𝒞 : DistributionClass Γ) : EntropyEstimable 𝒞 → EntropyGapTestable 𝒞 := by
  rintro ⟨E, time, ρ, r, est, hrun, hcomp, hsound⟩
  by_cases hne : ∃ n₀, ∃ D₀, D₀ ∈ 𝒞.members n₀
  swap
  · push_neg at hne
    exact ⟨E, 0, 0, 0, 1, 1, fun _ _ _ => 0, one_pos, one_pos,
      fun n D hD => absurd hD (hne n D), fun n D hD => absurd hD (hne n D)⟩
  obtain ⟨n₀, D₀, hD₀⟩ := hne
  let w₀ : Word Γ D₀.length := D₀.law.support_nonempty.some
  obtain ⟨T, timeT, hT⟩ := tester_runs 𝒞 E time ρ r est hrun n₀ D₀ hD₀ w₀
  obtain ⟨ρT, a, b, ha, hb, hgap⟩ := tester_gap hΓ 𝒞 ρ r est hcomp hsound
    (est n₀ 2 2 (blockList (fun _ : Fin (eval3 ρ n₀ 2 2) => w₀))
      (coinBits (fun _ : Fin (eval3 r n₀ 2 2) => false)))
  exact ⟨T, timeT, rT r, ρT, a, b, _, ha, hb,
    fun n D hD m xs ω => ⟨hT n D hD m xs ω, testFn_mem _ _ _ _ _ _ _⟩, hgap⟩

end

end AC55

theorem solution {Γ : Type} [Fintype Γ] (hΓ : 2 ≤ Fintype.card Γ)
    (𝒞 : AutoregressiveCompression.Main.DistributionClass Γ) :
    AutoregressiveCompression.Main.EntropyEstimable 𝒞 →
      AutoregressiveCompression.Main.EntropyGapTestable 𝒞 :=
  AC55.main (by omega) 𝒞
