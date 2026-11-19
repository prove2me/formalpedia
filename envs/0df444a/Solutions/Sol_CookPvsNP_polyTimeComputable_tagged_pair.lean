-- Prove2me | solution 1 for CookPvsNP.polyTimeComputable_tagged_pair
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:02:26.683934+00:00
-- url     : https://prove2.me/submissions/22f6ea90-8bb4-453e-99c4-4e88459e2f26

import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace CookPvsNP.TP

open CookPvsNP

section Generic

variable {Γ : Type} (M : TM Γ)

def mv : Move → ℤ
  | .left => -1
  | .right => 1

/-- `c` has state `q`, and its tape, read with absolute coordinates where the head is at `p`,
is `T`. -/
def Rel (c : Cfg Γ M.Q) (q : M.Q) (T : ℤ → Option Γ) (p : ℤ) : Prop :=
  c.state = q ∧ c.head = T p ∧ (∀ n : ℕ, c.right.getD n none = T (p + n + 1)) ∧
    (∀ n : ℕ, c.left.getD n none = T (p - n - 1))

def Halt (q : M.Q) : Prop := q = M.qaccept ∨ q = M.qreject

theorem headD_eq {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

theorem tail_getD {α : Type} (l : List α) (d : α) (n : ℕ) : l.tail.getD n d = l.getD (n + 1) d := by
  cases l <;> simp

theorem step_rel {c : Cfg Γ M.Q} {q : M.Q} {T : ℤ → Option Γ} {p : ℤ} (h : Rel M c q T p)
    (hq : ¬ Halt M q) {q' : M.Q} {s : Option Γ} {d : Move} (hδ : M.δ q (T p) = (q', s, d)) :
    Rel M (M.step c) q' (Function.update T p s) (p + mv d) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hnh : ¬ M.IsHalting c := by unfold TM.IsHalting; rw [h1]; exact hq
  have hδ' : M.δ c.state c.head = (q', s, d) := by rw [h1, h2]; exact hδ
  unfold TM.step
  rw [if_neg hnh, hδ']
  cases d with
  | right =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · show c.right.headD none = _
      rw [headD_eq, h3 0, Function.update_apply, if_neg (by simp [mv])]
      congr 1; simp [mv]
    · intro n
      show c.right.tail.getD n none = _
      rw [tail_getD, h3 (n + 1), Function.update_apply, if_neg (by simp [mv]; omega)]
      congr 1; simp only [mv]; push_cast; ring
    · intro n
      show (s :: c.left).getD n none = _
      cases n with
      | zero => simp [mv]
      | succ n =>
        rw [List.getD_cons_succ, h4 n, Function.update_apply, if_neg (by simp [mv]; omega)]
        congr 1; simp only [mv]; push_cast; ring
  | left =>
    cases hl : c.left with
    | nil =>
      have e : T (p - 1) = none := by
        have := h4 0; rw [hl] at this; simp at this; rw [← this]
      refine ⟨rfl, ?_, ?_, ?_⟩
      · show none = _
        rw [Function.update_apply, if_neg (by simp [mv])]
        simp [mv]; rw [← e]; congr 1
      · intro n
        show (s :: c.right).getD n none = _
        cases n with
        | zero => simp [mv]
        | succ n =>
          rw [List.getD_cons_succ, h3 n, Function.update_apply, if_neg (by simp [mv]; omega)]
          congr 1; simp only [mv]; push_cast; ring
      · intro n
        show ([] : List (Option Γ)).getD n none = _
        rw [Function.update_apply, if_neg (by simp [mv]; omega)]
        have := h4 (n + 1); rw [hl] at this; simp at this
        simp only [List.getD_nil]; rw [this]; congr 1; simp only [mv]; push_cast; ring
    | cons a l =>
      refine ⟨rfl, ?_, ?_, ?_⟩
      · show a = _
        have := h4 0; rw [hl] at this; simp at this
        rw [Function.update_apply, if_neg (by simp [mv]), this]
        congr 1
      · intro n
        show (s :: c.right).getD n none = _
        cases n with
        | zero => simp [mv]
        | succ n =>
          rw [List.getD_cons_succ, h3 n, Function.update_apply, if_neg (by simp [mv]; omega)]
          congr 1; simp only [mv]; push_cast; ring
      · intro n
        show l.getD n none = _
        have := h4 (n + 1); rw [hl, List.getD_cons_succ] at this
        rw [this, Function.update_apply, if_neg (by simp [mv]; omega)]
        congr 1; simp only [mv]; push_cast; ring

theorem run_succ (n : ℕ) (c : Cfg Γ M.Q) : M.run (n + 1) c = M.run n (M.step c) := by
  simp [TM.run, Function.iterate_succ_apply]

theorem run_add (a b : ℕ) (c : Cfg Γ M.Q) : M.run (a + b) c = M.run b (M.run a c) := by
  simp [TM.run, Nat.add_comm a b, Function.iterate_add_apply]

theorem run_zero (c : Cfg Γ M.Q) : M.run 0 c = c := rfl

theorem run_halting (n : ℕ) (c : Cfg Γ M.Q) (h : M.IsHalting c) : M.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : M.step c = c := by unfold TM.step; rw [if_pos h]
    rw [run_succ, hs, ih]

theorem run_mono {n N : ℕ} (c : Cfg Γ M.Q) (h : M.IsHalting (M.run n c)) (hN : n ≤ N) :
    M.run N c = M.run n c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [run_add, run_halting _ _ _ h]

theorem Rel.congrT {c : Cfg Γ M.Q} {q : M.Q} {T T' : ℤ → Option Γ} {p : ℤ} (h : Rel M c q T p)
    (e : T = T') : Rel M c q T' p := e ▸ h

theorem Rel.congrP {c : Cfg Γ M.Q} {q : M.Q} {T : ℤ → Option Γ} {p p' : ℤ} (h : Rel M c q T p)
    (e : p = p') : Rel M c q T p' := e ▸ h

theorem step_rel_keep {c : Cfg Γ M.Q} {q : M.Q} {T : ℤ → Option Γ} {p : ℤ} (h : Rel M c q T p)
    (hq : ¬ Halt M q) {q' : M.Q} {d : Move} (hδ : M.δ q (T p) = (q', T p, d)) :
    Rel M (M.step c) q' T (p + mv d) := by
  have := step_rel M h hq hδ
  rwa [Function.update_eq_self] at this

theorem sweep_right (q : M.Q) (hq : ¬ Halt M q) (P : Option Γ → Prop)
    (hδ : ∀ s, P s → M.δ q s = (q, s, .right)) :
    ∀ (n : ℕ) (c : Cfg Γ M.Q) (T : ℤ → Option Γ) (p : ℤ), Rel M c q T p →
      (∀ i : ℕ, i < n → P (T (p + i))) → Rel M (M.run n c) q T (p + n) := by
  intro n
  induction n with
  | zero => intro c T p h _; rw [run_zero]; simpa using h
  | succ n ih =>
    intro c T p h hP
    have h1 := step_rel_keep M h hq (hδ _ (by simpa using hP 0 (by omega)))
    rw [run_succ]
    have := ih _ T _ h1 (fun i hi => by
      have := hP (i + 1) (by omega); simp [mv] at this ⊢
      rw [show p + 1 + (i : ℤ) = p + ((i : ℤ) + 1) by ring]; exact this)
    rw [show p + ((n + 1 : ℕ) : ℤ) = p + mv Move.right + n by simp [mv]; ring]
    exact this

theorem sweep_left (q : M.Q) (hq : ¬ Halt M q) (P : Option Γ → Prop)
    (hδ : ∀ s, P s → M.δ q s = (q, s, .left)) :
    ∀ (n : ℕ) (c : Cfg Γ M.Q) (T : ℤ → Option Γ) (p : ℤ), Rel M c q T p →
      (∀ i : ℕ, i < n → P (T (p - i))) → Rel M (M.run n c) q T (p - n) := by
  intro n
  induction n with
  | zero => intro c T p h _; rw [run_zero]; simpa using h
  | succ n ih =>
    intro c T p h hP
    have h1 := step_rel_keep M h hq (hδ _ (by simpa using hP 0 (by omega)))
    rw [run_succ]
    have := ih _ T _ h1 (fun i hi => by
      have := hP (i + 1) (by omega); simp [mv] at this ⊢
      rw [show p + -1 - (i : ℤ) = p - ((i : ℤ) + 1) by ring]; exact this)
    rw [show p - ((n + 1 : ℕ) : ℤ) = p + mv Move.left - n by simp [mv]; ring]
    exact this

theorem sweep_right_to (q : M.Q) (hq : ¬ Halt M q) (P : Option Γ → Prop)
    (hδ : ∀ s, P s → M.δ q s = (q, s, .right)) (c : Cfg Γ M.Q) (T : ℤ → Option Γ) (p r : ℤ)
    (h : Rel M c q T p) (hpr : p ≤ r) (hP : ∀ i, p ≤ i → i < r → P (T i)) :
    Rel M (M.run (r - p).toNat c) q T r := by
  have := sweep_right M q hq P hδ (r - p).toNat c T p h (fun i hi => hP _ (by omega) (by omega))
  rwa [show p + ((r - p).toNat : ℤ) = r by omega] at this

theorem sweep_left_to (q : M.Q) (hq : ¬ Halt M q) (P : Option Γ → Prop)
    (hδ : ∀ s, P s → M.δ q s = (q, s, .left)) (c : Cfg Γ M.Q) (T : ℤ → Option Γ) (p r : ℤ)
    (h : Rel M c q T p) (hrp : r ≤ p) (hP : ∀ i, r < i → i ≤ p → P (T i)) :
    Rel M (M.run (p - r).toNat c) q T r := by
  have := sweep_left M q hq P hδ (p - r).toNat c T p h (fun i hi => hP _ (by omega) (by omega))
  rwa [show p - ((p - r).toNat : ℤ) = r by omega] at this

/-- The tape of the initial configuration. -/
def initTape (w : List Γ) (i : ℤ) : Option Γ := if 0 ≤ i then w[i.toNat]? else none

theorem init_rel (w : List Γ) : Rel M (M.init w) M.q₀ (initTape w) 0 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · cases w <;> simp [TM.init, initTape]
  · intro n
    show (w.map some).tail.getD n none = _
    rw [tail_getD]
    simp [initTape]
    rw [if_pos (by omega)]
    cases w[n+1]? <;> rfl
  · intro n
    show ([] : List (Option Γ)).getD n none = _
    simp [initTape]; omega


/-! ### Output lemmas -/

def strip (l : List (Option Γ)) : List (Option Γ) := (l.reverse.dropWhile Option.isNone).reverse

theorem output_eq (c : Cfg Γ M.Q) : M.output c = strip (c.head :: c.right) := rfl

theorem rel_getD {c : Cfg Γ M.Q} {q : M.Q} {T : ℤ → Option Γ} {p : ℤ} (h : Rel M c q T p) :
    ∀ n : ℕ, (c.head :: c.right).getD n none = T (p + n) := by
  intro n
  cases n with
  | zero => simpa using h.2.1
  | succ n =>
    rw [List.getD_cons_succ, h.2.2.1 n]; congr 1; push_cast; ring

theorem strip_decomp (L : List (Option Γ)) :
    ∃ N : List (Option Γ), L = strip L ++ N ∧ ∀ y ∈ N, y = none := by
  refine ⟨(L.reverse.takeWhile Option.isNone).reverse, ?_, ?_⟩
  · unfold strip
    rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]
  · intro y hy
    have := List.mem_takeWhile_imp (List.mem_reverse.mp hy)
    simpa using this

theorem getD_of_strip (L : List (Option Γ)) (l : List Γ) (h : strip L = l.map some) :
    ∀ n : ℕ, L.getD n none = l[n]? := by
  intro n
  obtain ⟨N, hL, hN⟩ := strip_decomp L
  rw [h] at hL
  rw [hL, List.getD_eq_getElem?_getD]
  by_cases hn : n < l.length
  · rw [List.getElem?_append_left (by simpa using hn)]
    simp
    cases l[n]? <;> rfl
  · rw [List.getElem?_append_right (by simp; omega)]
    have : l[n]? = none := by simp; omega
    rw [this]
    cases hk : N[n - (l.map some).length]? with
    | none => rfl
    | some y => exact hN y (List.mem_of_getElem? hk)

theorem strip_nil_of (L : List (Option Γ)) (h : ∀ y ∈ L, y = none) : strip L = [] := by
  unfold strip
  rw [List.reverse_eq_nil_iff, List.dropWhile_eq_nil_iff]
  intro y hy
  obtain rfl := h y (List.mem_reverse.mp hy)
  rfl

theorem strip_cons_some (a : Γ) (L : List (Option Γ)) : strip (some a :: L) = some a :: strip L := by
  unfold strip
  rw [List.reverse_cons, List.dropWhile_append]
  split_ifs with he
  · rw [List.isEmpty_iff] at he
    rw [he]; simp
  · simp

theorem strip_of_getD (L : List (Option Γ)) (l : List Γ) (h : ∀ n : ℕ, L.getD n none = l[n]?) :
    strip L = l.map some := by
  induction l generalizing L with
  | nil =>
    simp only [List.map_nil]
    apply strip_nil_of
    intro y hy
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hy
    have := h n
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn] at this
    simpa using this
  | cons b l ih =>
    cases L with
    | nil => have := h 0; simp at this
    | cons y L =>
      have h0 := h 0
      simp at h0
      subst h0
      rw [strip_cons_some, ih L (fun n => by simpa using h (n + 1))]
      simp

theorem output_of_rel {c : Cfg Γ M.Q} {q : M.Q} {T : ℤ → Option Γ} {p : ℤ} (h : Rel M c q T p)
    (l : List Γ) (hl : ∀ n : ℕ, T (p + n) = l[n]?) : M.output c = l.map some := by
  rw [output_eq]
  exact strip_of_getD _ _ (fun n => by rw [rel_getD M h n, hl n])

theorem tape_of_output {c : Cfg Γ M.Q} {q : M.Q} {T : ℤ → Option Γ} {p : ℤ} (h : Rel M c q T p)
    (l : List Γ) (hl : M.output c = l.map some) : ∀ n : ℕ, T (p + n) = l[n]? := by
  intro n
  rw [← rel_getD M h n]
  exact getD_of_strip _ _ hl n

/-! ### Regions and simulation invariants -/

def Region (T : ℤ → Option Γ) (lo hi : ℤ) : Prop :=
  ∀ i, (T i).isSome = true ↔ (lo ≤ i ∧ i ≤ hi)

def InvS (er : Option Γ → Option Γ) (Pc : Option Γ → Prop) (T0 : ℤ → Option Γ) (L0 H0 : ℤ)
    (k : ℕ) (T : ℤ → Option Γ) (p : ℤ) : Prop :=
  (∃ lo hi, Region T lo hi ∧ lo ≤ p + 1 ∧ p ≤ hi + 1 ∧ L0 - k ≤ lo ∧ lo ≤ L0 ∧ H0 ≤ hi ∧
    hi ≤ H0 + k) ∧ (∀ i, er (T i) = er (T0 i)) ∧ -(k : ℤ) ≤ p ∧ p ≤ k ∧ (∀ i, Pc (T i))

theorem InvS_step (er : Option Γ → Option Γ) (Pc : Option Γ → Prop) (T0 : ℤ → Option Γ)
    (L0 H0 : ℤ) (hL0 : L0 ≤ 0)
    (hH0 : 0 ≤ H0) {Γ' : Type} (set : Option Γ → Option Γ' → Option Γ)
    (hs : ∀ s w, (set s w).isSome = true) (her : ∀ s w, er (set s w) = er s)
    (hPc : ∀ s w, Pc (set s w))
    (k : ℕ) (T : ℤ → Option Γ) (p : ℤ) (w : Option Γ') (d : Move)
    (h : InvS er Pc T0 L0 H0 k T p) :
    InvS er Pc T0 L0 H0 (k + 1) (Function.update T p (set (T p) w)) (p + mv d) := by
  obtain ⟨⟨lo, hi, hR, h1, h2, h3, h4, h5, h6⟩, he, hp1, hp2, hpc⟩ := h
  have hmv : mv d = 1 ∨ mv d = -1 := by cases d <;> simp [mv]
  refine ⟨⟨min lo p, max hi p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi' : i = p
    · subst hi'; simp [hs]
    · rw [Function.update_of_ne hi', hR i]; omega
  all_goals try (push_cast; omega)
  · intro i
    by_cases hi' : i = p
    · subst hi'; simp [her, he]
    · rw [Function.update_of_ne hi', he i]
  · intro i
    by_cases hi' : i = p
    · subst hi'; simp [hPc]
    · rw [Function.update_of_ne hi']; exact hpc i

/-! ### Simulation -/

theorem simulate {Γ' : Type} (M' : TM Γ') (emb : M'.Q → M.Q) (get : Option Γ → Option Γ')
    (set : Option Γ → Option Γ' → Option Γ) (hget : ∀ s w, get (set s w) = w)
    (hnh : ∀ q, ¬ Halt M (emb q))
    (hδ : ∀ q s, ¬ Halt M' q → M.δ (emb q) s =
      (emb (M'.δ q (get s)).1, set s (M'.δ q (get s)).2.1, (M'.δ q (get s)).2.2))
    (Inv : ℕ → (ℤ → Option Γ) → ℤ → Prop)
    (hInv : ∀ k T p w d, Inv k T p → Inv (k + 1) (Function.update T p (set (T p) w)) (p + mv d)) :
    ∀ (n k : ℕ) (c : Cfg Γ M.Q) (c' : Cfg Γ' M'.Q) (T : ℤ → Option Γ) (p : ℤ),
      Rel M c (emb c'.state) T p → Rel M' c' c'.state (fun i => get (T i)) p → Inv k T p →
      (∀ m < n, ¬ Halt M' (M'.run m c').state) →
      ∃ T' p', Rel M (M.run n c) (emb (M'.run n c').state) T' p' ∧
        Rel M' (M'.run n c') (M'.run n c').state (fun i => get (T' i)) p' ∧ Inv (k + n) T' p' := by
  intro n
  induction n with
  | zero => intro k c c' T p h1 h2 h3 _; exact ⟨T, p, h1, h2, h3⟩
  | succ n ih =>
    intro k c c' T p h1 h2 h3 hh
    have hn0 : ¬ Halt M' c'.state := hh 0 (by omega)
    rcases hr : M'.δ c'.state (get (T p)) with ⟨q', w, d⟩
    have hδ' : M.δ (emb c'.state) (T p) = (emb q', set (T p) w, d) := by
      rw [hδ _ _ hn0, hr]
    have s1 := step_rel M h1 (hnh _) hδ'
    have s2 := step_rel M' h2 hn0 (q' := q') (s := w) (d := d) hr
    have hst : (M'.step c').state = q' := s2.1
    have s2' : Rel M' (M'.step c') (M'.step c').state
        (fun i => get (Function.update T p (set (T p) w) i)) (p + mv d) := by
      rw [hst]
      refine Rel.congrT M' s2 ?_
      funext i
      by_cases hi : i = p
      · subst hi; simp [hget]
      · simp [Function.update_of_ne hi]
    rw [← hst] at s1
    obtain ⟨T', p', r1, r2, r3⟩ := ih (k + 1) (M.step c) (M'.step c') _ _ s1 s2' (hInv _ _ _ _ _ h3)
      (fun m hm => by have := hh (m + 1) (by omega); rwa [run_succ] at this)
    refine ⟨T', p', ?_, ?_, ?_⟩
    · rw [run_succ, run_succ]; exact r1
    · rw [run_succ]; exact r2
    · rwa [show k + (n + 1) = k + 1 + n by omega]


end Generic


/-! ## The machine -/

inductive Sym (Γf Γg B C : Type)
  | work (a : Option Γf) (b : Option Γg) (org fs gs : Bool)
  | out (o : Option (B ⊕ C))
  deriving Fintype

inductive St (Qf Qg B C : Type)
  | start | back0 | sim1 (q : Qf) | goEnd1 | findOrg | toSim2 | sim2 (q : Qg) | goEnd2
  | find (w : Bool) | mark (w : Bool) (o : B ⊕ C) | carry (w : Bool) (o : Option (B ⊕ C))
  | goEndFin | backOut | acc | rej
  deriving Fintype

section Machine

variable {Γf Γg B C : Type}

def W : Option (Sym Γf Γg B C) → Sym Γf Γg B C
  | none => .work none none false false false
  | some x => x

def tr1 (s : Option (Sym Γf Γg B C)) : Option Γf :=
  match W s with
  | .work a _ _ _ _ => a
  | .out _ => none

def tr2 (s : Option (Sym Γf Γg B C)) : Option Γg :=
  match W s with
  | .work _ b _ _ _ => b
  | .out _ => none

def orgOf (s : Option (Sym Γf Γg B C)) : Bool :=
  match W s with
  | .work _ _ o _ _ => o
  | .out _ => false

def flag (w : Bool) (s : Option (Sym Γf Γg B C)) : Bool :=
  match W s with
  | .work _ _ _ f g => if w then g else f
  | .out _ => false

def set1 (s : Option (Sym Γf Γg B C)) (v : Option Γf) : Option (Sym Γf Γg B C) :=
  some (match W s with
    | .work _ b o f g => .work v b o f g
    | .out _ => .work v none false false false)

def set2 (s : Option (Sym Γf Γg B C)) (v : Option Γg) : Option (Sym Γf Γg B C) :=
  some (match W s with
    | .work a _ o f g => .work a v o f g
    | .out _ => .work none v false false false)

def setOrg (s : Option (Sym Γf Γg B C)) : Option (Sym Γf Γg B C) :=
  some (match W s with
    | .work a b _ f g => .work a b true f g
    | .out o => .out o)

def setFlag (w : Bool) (s : Option (Sym Γf Γg B C)) (v : Bool) : Option (Sym Γf Γg B C) :=
  some (match W s with
    | .work a b o f g => if w then .work a b o f v else .work a b o v g
    | .out o => .out o)

def flags (s : Option (Sym Γf Γg B C)) (u v : Bool) : Option (Sym Γf Γg B C) :=
  match s with
  | some (.work a b o _ _) => some (.work a b o u v)
  | s => s

def pad : Option (Sym Γf Γg B C) := some (.work none none false false false)

def IsW (s : Option (Sym Γf Γg B C)) : Prop := ∃ a b o f g, s = some (.work a b o f g)

def IsW0 (s : Option (Sym Γf Γg B C)) : Prop := ∃ a b o, s = some (.work a b o false false)

def isOut (s : Option (Sym Γf Γg B C)) : Bool :=
  match s with
  | some (.out _) => true
  | _ => false

noncomputable def dec {X Y : Type} (ι : X ↪ Y) (y : Y) : Option X := by
  classical
  exact if h : ∃ x, ι x = y then some h.choose else none

theorem dec_emb {X Y : Type} (ι : X ↪ Y) (x : X) : dec ι (ι x) = some x := by
  unfold dec
  have h : ∃ x', ι x' = ι x := ⟨x, rfl⟩
  rw [dif_pos h]
  congr 1
  exact ι.injective h.choose_spec

noncomputable def trk (ιfo : B ↪ Γf) (ιgo : C ↪ Γg) (w : Bool) (s : Option (Sym Γf Γg B C)) :
    Option (B ⊕ C) :=
  if w then ((tr2 s).bind (dec ιgo)).map Sum.inr else ((tr1 s).bind (dec ιfo)).map Sum.inl

variable (ιfo : B ↪ Γf) (ιgo : C ↪ Γg) (Mf : TM Γf) (Mg : TM Γg)

noncomputable def delta : St Mf.Q Mg.Q B C → Option (Sym Γf Γg B C) →
    St Mf.Q Mg.Q B C × Option (Sym Γf Γg B C) × Move
  | .start, s => (.back0, setOrg s, .right)
  | .back0, s => (.sim1 Mf.q₀, s, .left)
  | .sim1 q, s =>
    if q = Mf.qaccept ∨ q = Mf.qreject then (.goEnd1, setFlag false s true, .right)
    else (.sim1 (Mf.δ q (tr1 s)).1, set1 s (Mf.δ q (tr1 s)).2.1, (Mf.δ q (tr1 s)).2.2)
  | .goEnd1, none => (.findOrg, none, .left)
  | .goEnd1, some x => (.goEnd1, some x, .right)
  | .findOrg, s => if orgOf s then (.toSim2, s, .left) else (.findOrg, s, .left)
  | .toSim2, s => (.sim2 Mg.q₀, s, .right)
  | .sim2 q, s =>
    if q = Mg.qaccept ∨ q = Mg.qreject then (.goEnd2, setFlag true s true, .right)
    else (.sim2 (Mg.δ q (tr2 s)).1, set2 s (Mg.δ q (tr2 s)).2.1, (Mg.δ q (tr2 s)).2.2)
  | .goEnd2, none => (.find false, pad, .left)
  | .goEnd2, some x => (.goEnd2, some x, .right)
  | .find w, s =>
    if flag w s then
      (match trk ιfo ιgo w s with
        | some o => (.mark w o, setFlag w s false, .right)
        | none => (if w then .goEndFin else .carry true none, s, .right))
    else (.find w, s, .left)
  | .mark w o, s => (.carry w (some o), setFlag w s true, .right)
  | .carry w o, none => (.find w, some (.out o), .left)
  | .carry w o, some x => (.carry w o, some x, .right)
  | .goEndFin, none => (.backOut, none, .left)
  | .goEndFin, some x => (.goEndFin, some x, .right)
  | .backOut, some (.out o) => (.backOut, some (.out o), .left)
  | .backOut, none => (.acc, none, .right)
  | .backOut, some (.work a b o f g) => (.acc, some (.work a b o f g), .right)
  | .acc, s => (.acc, s, .right)
  | .rej, s => (.rej, s, .right)

noncomputable def CM [Fintype B] [Fintype C] : TM (Sym Γf Γg B C) where
  Q := St Mf.Q Mg.Q B C
  finQ := inferInstance
  decQ := Classical.decEq _
  q₀ := .start
  qaccept := .acc
  qreject := .rej
  accept_ne_reject := by intro h; cases h
  δ := delta ιfo ιgo Mf Mg

variable [Fintype B] [Fintype C]

theorem nh {q : St Mf.Q Mg.Q B C} (h1 : q ≠ .acc) (h2 : q ≠ .rej) :
    ¬ Halt (CM ιfo ιgo Mf Mg) q := by
  rintro (h | h)
  · exact h1 h
  · exact h2 h

end Machine


section Cells

variable {Γf Γg B C : Type}

def er1 (s : Option (Sym Γf Γg B C)) : Option (Sym Γf Γg B C) := set1 s none
def er2 (s : Option (Sym Γf Γg B C)) : Option (Sym Γf Γg B C) := set2 s none
def Pc (s : Option (Sym Γf Γg B C)) : Prop := s = none ∨ IsW s

theorem tr1_set1 (s : Option (Sym Γf Γg B C)) (v : Option Γf) : tr1 (set1 s v) = v := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem tr2_set2 (s : Option (Sym Γf Γg B C)) (v : Option Γg) : tr2 (set2 s v) = v := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem set1_isSome (s : Option (Sym Γf Γg B C)) (v : Option Γf) : (set1 s v).isSome = true := rfl
theorem set2_isSome (s : Option (Sym Γf Γg B C)) (v : Option Γg) : (set2 s v).isSome = true := rfl
theorem er1_set1 (s : Option (Sym Γf Γg B C)) (v : Option Γf) : er1 (set1 s v) = er1 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem er2_set2 (s : Option (Sym Γf Γg B C)) (v : Option Γg) : er2 (set2 s v) = er2 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem Pc_set1 (s : Option (Sym Γf Γg B C)) (v : Option Γf) : Pc (set1 s v) := by
  right; rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> exact ⟨_, _, _, _, _, rfl⟩
theorem Pc_set2 (s : Option (Sym Γf Γg B C)) (v : Option Γg) : Pc (set2 s v) := by
  right; rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> exact ⟨_, _, _, _, _, rfl⟩

theorem tr2_er1 (s : Option (Sym Γf Γg B C)) : tr2 (er1 s) = tr2 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem org_er1 (s : Option (Sym Γf Γg B C)) : orgOf (er1 s) = orgOf s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem flag_er1 (w : Bool) (s : Option (Sym Γf Γg B C)) : flag w (er1 s) = flag w s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> cases w <;> rfl
theorem tr1_er2 (s : Option (Sym Γf Γg B C)) : tr1 (er2 s) = tr1 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem flag_er2 (w : Bool) (s : Option (Sym Γf Γg B C)) : flag w (er2 s) = flag w s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> cases w <;> rfl

theorem tr1_setFlag (w : Bool) (s : Option (Sym Γf Γg B C)) (v : Bool) :
    tr1 (setFlag w s v) = tr1 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> cases w <;> rfl
theorem tr2_setFlag (w : Bool) (s : Option (Sym Γf Γg B C)) (v : Bool) :
    tr2 (setFlag w s v) = tr2 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> cases w <;> rfl
theorem org_setFlag (w : Bool) (s : Option (Sym Γf Γg B C)) (v : Bool) :
    orgOf (setFlag w s v) = orgOf s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> cases w <;> rfl
theorem flag_setFlag_self (w : Bool) (s : Option (Sym Γf Γg B C)) (hs : Pc s) (v : Bool) :
    flag w (setFlag w s v) = v := by
  rcases hs with rfl | ⟨a, b, o, f, g, rfl⟩ <;> cases w <;> rfl
theorem flag_true_setFlag_false (s : Option (Sym Γf Γg B C)) (v : Bool) :
    flag true (setFlag false s v) = flag true s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem flag_false_setFlag_true (s : Option (Sym Γf Γg B C)) (v : Bool) :
    flag false (setFlag true s v) = flag false s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem Pc_setFlag (w : Bool) (s : Option (Sym Γf Γg B C)) (v : Bool) (hs : Pc s) :
    Pc (setFlag w s v) := by
  right; rcases hs with rfl | ⟨a, b, o, f, g, rfl⟩ <;> cases w <;> exact ⟨_, _, _, _, _, rfl⟩
theorem setFlag_isSome (w : Bool) (s : Option (Sym Γf Γg B C)) (v : Bool) :
    (setFlag w s v).isSome = true := rfl

theorem tr1_setOrg (s : Option (Sym Γf Γg B C)) : tr1 (setOrg s) = tr1 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem tr2_setOrg (s : Option (Sym Γf Γg B C)) : tr2 (setOrg s) = tr2 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem flag_setOrg (w : Bool) (s : Option (Sym Γf Γg B C)) : flag w (setOrg s) = flag w s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl

theorem flags_flags (s : Option (Sym Γf Γg B C)) (hs : IsW s) :
    flags (flags s false false) (flag false s) (flag true s) = s := by
  obtain ⟨a, b, o, f, g, rfl⟩ := hs; rfl
theorem IsW0_flags (s : Option (Sym Γf Γg B C)) (hs : IsW s) : IsW0 (flags s false false) := by
  obtain ⟨a, b, o, f, g, rfl⟩ := hs; exact ⟨a, b, o, rfl⟩
theorem flag_false_flags (s : Option (Sym Γf Γg B C)) (hs : IsW0 s) (u v : Bool) :
    flag false (flags s u v) = u := by
  obtain ⟨a, b, o, rfl⟩ := hs; rfl
theorem flag_true_flags (s : Option (Sym Γf Γg B C)) (hs : IsW0 s) (u v : Bool) :
    flag true (flags s u v) = v := by
  obtain ⟨a, b, o, rfl⟩ := hs; rfl
theorem tr1_flags (s : Option (Sym Γf Γg B C)) (u v : Bool) : tr1 (flags s u v) = tr1 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem tr2_flags (s : Option (Sym Γf Γg B C)) (u v : Bool) : tr2 (flags s u v) = tr2 s := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o <;> rfl
theorem setFlag_false_flags (s : Option (Sym Γf Γg B C)) (hs : IsW0 s) (u v b : Bool) :
    setFlag false (flags s u v) b = flags s b v := by
  obtain ⟨a, b, o, rfl⟩ := hs; rfl
theorem setFlag_true_flags (s : Option (Sym Γf Γg B C)) (hs : IsW0 s) (u v b : Bool) :
    setFlag true (flags s u v) b = flags s u b := by
  obtain ⟨a, b, o, rfl⟩ := hs; rfl
theorem flags_isSome (s : Option (Sym Γf Γg B C)) (hs : IsW0 s) (u v : Bool) :
    (flags s u v).isSome = true := by
  obtain ⟨a, b, o, rfl⟩ := hs; rfl
theorem trk_flags (ιfo : B ↪ Γf) (ιgo : C ↪ Γg) (w : Bool) (s : Option (Sym Γf Γg B C))
    (u v : Bool) : trk ιfo ιgo w (flags s u v) = trk ιfo ιgo w s := by
  unfold trk; rw [tr1_flags, tr2_flags]
theorem flag_out (w : Bool) (o : Option (Sym Γf Γg B C)) (h : ∀ x, o = some x → isOut o = true) :
    flag w o = false := by
  rcases o with _ | ⟨a, b, o, f, g⟩ | o
  · cases w <;> rfl
  · simp [isOut] at h
  · rfl

end Cells

section Steps

variable {Γf Γg B C : Type} [Fintype B] [Fintype C]
variable (ιfo : B ↪ Γf) (ιgo : C ↪ Γg) (Mf : TM Γf) (Mg : TM Γg)

theorem d_start (s : Option (Sym Γf Γg B C)) :
    (CM ιfo ιgo Mf Mg).δ .start s = (.back0, setOrg s, .right) := rfl
theorem d_back0 (s : Option (Sym Γf Γg B C)) :
    (CM ιfo ιgo Mf Mg).δ .back0 s = (.sim1 Mf.q₀, s, .left) := rfl
theorem d_sim1_halt (q : Mf.Q) (hq : Halt Mf q) (s : Option (Sym Γf Γg B C)) :
    (CM ιfo ιgo Mf Mg).δ (.sim1 q) s = (.goEnd1, setFlag false s true, .right) := by
  have hq' : q = _ ∨ q = _ := hq
  simp [CM, delta, hq']
theorem d_sim1 (q : Mf.Q) (hq : ¬ Halt Mf q) (s : Option (Sym Γf Γg B C)) :
    (CM ιfo ιgo Mf Mg).δ (.sim1 q) s =
      (.sim1 (Mf.δ q (tr1 s)).1, set1 s (Mf.δ q (tr1 s)).2.1, (Mf.δ q (tr1 s)).2.2) := by
  have hq' : ¬ (q = _ ∨ q = _) := hq
  simp [CM, delta, hq']
theorem d_sim2_halt (q : Mg.Q) (hq : Halt Mg q) (s : Option (Sym Γf Γg B C)) :
    (CM ιfo ιgo Mf Mg).δ (.sim2 q) s = (.goEnd2, setFlag true s true, .right) := by
  have hq' : q = _ ∨ q = _ := hq
  simp [CM, delta, hq']
theorem d_sim2 (q : Mg.Q) (hq : ¬ Halt Mg q) (s : Option (Sym Γf Γg B C)) :
    (CM ιfo ιgo Mf Mg).δ (.sim2 q) s =
      (.sim2 (Mg.δ q (tr2 s)).1, set2 s (Mg.δ q (tr2 s)).2.1, (Mg.δ q (tr2 s)).2.2) := by
  have hq' : ¬ (q = _ ∨ q = _) := hq
  simp [CM, delta, hq']
theorem d_goEnd1_some (s : Option (Sym Γf Γg B C)) (hs : s.isSome = true) :
    (CM ιfo ιgo Mf Mg).δ .goEnd1 s = (.goEnd1, s, .right) := by
  rcases s with _ | x
  · simp at hs
  · rfl
theorem d_goEnd1_none :
    (CM ιfo ιgo Mf Mg).δ .goEnd1 none = (.findOrg, none, .left) := rfl
theorem d_findOrg_no (s : Option (Sym Γf Γg B C)) (hs : orgOf s = false) :
    (CM ιfo ιgo Mf Mg).δ .findOrg s = (.findOrg, s, .left) := by
  simp [CM, delta, hs]
theorem d_findOrg_yes (s : Option (Sym Γf Γg B C)) (hs : orgOf s = true) :
    (CM ιfo ιgo Mf Mg).δ .findOrg s = (.toSim2, s, .left) := by
  simp [CM, delta, hs]
theorem d_toSim2 (s : Option (Sym Γf Γg B C)) :
    (CM ιfo ιgo Mf Mg).δ .toSim2 s = (.sim2 Mg.q₀, s, .right) := rfl
theorem d_goEnd2_some (s : Option (Sym Γf Γg B C)) (hs : s.isSome = true) :
    (CM ιfo ιgo Mf Mg).δ .goEnd2 s = (.goEnd2, s, .right) := by
  rcases s with _ | x
  · simp at hs
  · rfl
theorem d_goEnd2_none :
    (CM ιfo ιgo Mf Mg).δ .goEnd2 none = (.find false, pad, .left) := rfl
theorem d_find_no (w : Bool) (s : Option (Sym Γf Γg B C)) (hs : flag w s = false) :
    (CM ιfo ιgo Mf Mg).δ (.find w) s = (.find w, s, .left) := by
  simp [CM, delta, hs]
theorem d_find_some (w : Bool) (s : Option (Sym Γf Γg B C)) (hs : flag w s = true) (o : B ⊕ C)
    (ho : trk ιfo ιgo w s = some o) :
    (CM ιfo ιgo Mf Mg).δ (.find w) s = (.mark w o, setFlag w s false, .right) := by
  simp [CM, delta, hs, ho]
theorem d_find_none (w : Bool) (s : Option (Sym Γf Γg B C)) (hs : flag w s = true)
    (ho : trk ιfo ιgo w s = none) :
    (CM ιfo ιgo Mf Mg).δ (.find w) s = (if w then .goEndFin else .carry true none, s, .right) := by
  simp [CM, delta, hs, ho]
theorem d_mark (w : Bool) (o : B ⊕ C) (s : Option (Sym Γf Γg B C)) :
    (CM ιfo ιgo Mf Mg).δ (.mark w o) s = (.carry w (some o), setFlag w s true, .right) := rfl
theorem d_carry_some (w : Bool) (o : Option (B ⊕ C)) (s : Option (Sym Γf Γg B C))
    (hs : s.isSome = true) :
    (CM ιfo ιgo Mf Mg).δ (.carry w o) s = (.carry w o, s, .right) := by
  rcases s with _ | x
  · simp at hs
  · rfl
theorem d_carry_none (w : Bool) (o : Option (B ⊕ C)) :
    (CM ιfo ιgo Mf Mg).δ (.carry w o) none = (.find w, some (.out o), .left) := rfl
theorem d_goEndFin_some (s : Option (Sym Γf Γg B C)) (hs : s.isSome = true) :
    (CM ιfo ιgo Mf Mg).δ .goEndFin s = (.goEndFin, s, .right) := by
  rcases s with _ | x
  · simp at hs
  · rfl
theorem d_goEndFin_none :
    (CM ιfo ιgo Mf Mg).δ .goEndFin none = (.backOut, none, .left) := rfl
theorem d_backOut_out (s : Option (Sym Γf Γg B C)) (hs : isOut s = true) :
    (CM ιfo ιgo Mf Mg).δ .backOut s = (.backOut, s, .left) := by
  rcases s with _ | ⟨a, b, o, f, g⟩ | o
  · simp [isOut] at hs
  · simp [isOut] at hs
  · rfl
theorem d_backOut_work (s : Option (Sym Γf Γg B C)) (hs : IsW s) :
    (CM ιfo ιgo Mf Mg).δ .backOut s = (.acc, s, .right) := by
  obtain ⟨a, b, o, f, g, rfl⟩ := hs; rfl

end Steps


section Transport

variable {Γf Γg B C : Type} [Fintype B] [Fintype C]
variable (ιfo : B ↪ Γf) (ιgo : C ↪ Γg) (Mf : TM Γf) (Mg : TM Γg)

/-- The tape during the transport phases: the work region (up to `R`) with cursor flags at
`cf` (first flag) and `cg` (second flag), followed by the output cells `O`. -/
def TT (Z : ℤ → Option (Sym Γf Γg B C)) (R cf cg : ℤ) (O : List (Option (B ⊕ C))) (i : ℤ) :
    Option (Sym Γf Γg B C) :=
  if i ≤ R then flags (Z i) (decide (i = cf)) (decide (i = cg))
  else (O[(i - R - 1).toNat]?).map Sym.out

/-- The tape with the moving cursor `c` of kind `w` and the fixed cursor `d` of the other kind. -/
def TTw (w : Bool) (Z : ℤ → Option (Sym Γf Γg B C)) (R c d : ℤ) (O : List (Option (B ⊕ C))) :
    ℤ → Option (Sym Γf Γg B C) :=
  if w then TT Z R d c O else TT Z R c d O

theorem run_one (c : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q) :
    (CM ιfo ιgo Mf Mg).run 1 c = (CM ιfo ιgo Mf Mg).step c := rfl

variable {Z : ℤ → Option (Sym Γf Γg B C)} {R lo : ℤ}

theorem TTw_flag_ne (hZ : ∀ i, lo ≤ i → i ≤ R → IsW0 (Z i)) (w : Bool) (c d : ℤ) (O) (i : ℤ)
    (hi : lo ≤ i) (hic : i ≠ c) : flag w (TTw w Z R c d O i) = false := by
  unfold TTw TT
  by_cases hR : i ≤ R
  · cases w
    · simp only [if_neg Bool.false_ne_true, if_pos hR]
      rw [flag_false_flags _ (hZ i hi hR)]; simp [hic]
    · simp only [if_pos hR, if_true]
      rw [flag_true_flags _ (hZ i hi hR)]; simp [hic]
  · cases w <;> simp only [if_neg hR, if_true, if_neg Bool.false_ne_true] <;>
      rcases (O[(i - R - 1).toNat]?) with _ | o <;> rfl

theorem TTw_flag_c (hZ : ∀ i, lo ≤ i → i ≤ R → IsW0 (Z i)) (w : Bool) (c d : ℤ) (O)
    (hc : lo ≤ c) (hcR : c ≤ R) : flag w (TTw w Z R c d O c) = true := by
  unfold TTw TT
  cases w
  · simp only [if_neg Bool.false_ne_true, if_pos hcR]
    rw [flag_false_flags _ (hZ c hc hcR)]; simp
  · simp only [if_pos hcR, if_true]
    rw [flag_true_flags _ (hZ c hc hcR)]; simp

theorem TTw_trk (w : Bool) (c d : ℤ) (O) (i : ℤ) (hR : i ≤ R) :
    trk ιfo ιgo w (TTw w Z R c d O i) = trk ιfo ιgo w (Z i) := by
  unfold TTw TT
  cases w <;> simp only [if_pos hR, if_true, if_neg Bool.false_ne_true] <;> rw [trk_flags]

theorem TTw_isSome (hZ : ∀ i, lo ≤ i → i ≤ R → IsW0 (Z i)) (w : Bool) (c d : ℤ) (O) (i : ℤ)
    (hi : lo ≤ i) (hi2 : i ≤ R + O.length) : (TTw w Z R c d O i).isSome = true := by
  unfold TTw TT
  by_cases hR : i ≤ R
  · cases w <;> simp only [if_pos hR, if_true, if_neg Bool.false_ne_true] <;>
      exact flags_isSome _ (hZ i hi hR) _ _
  · have hk : (i - R - 1).toNat < O.length := by omega
    cases w <;> simp only [if_neg hR, if_true, if_neg Bool.false_ne_true] <;>
      rw [List.getElem?_eq_getElem hk] <;> rfl

theorem TTw_isOut (w : Bool) (c d : ℤ) (O) (i : ℤ)
    (hi : R < i) (hi2 : i ≤ R + O.length) : isOut (TTw w Z R c d O i) = true := by
  unfold TTw TT
  have hR : ¬ i ≤ R := by omega
  have hk : (i - R - 1).toNat < O.length := by omega
  cases w <;> simp only [if_neg hR, if_true, if_neg Bool.false_ne_true] <;>
    rw [List.getElem?_eq_getElem hk] <;> rfl

theorem TTw_end (w : Bool) (c d : ℤ) (O) :
    TTw w Z R c d O (R + O.length + 1) = none := by
  unfold TTw TT
  have hR : ¬ R + O.length + 1 ≤ R := by omega
  have hk : (R + O.length + 1 - R - 1).toNat = O.length := by omega
  cases w <;> simp only [if_neg hR, if_true, if_neg Bool.false_ne_true] <;> simp [hk]

theorem TTw_append (w : Bool) (c d : ℤ) (O) (o : Option (B ⊕ C)) :
    Function.update (TTw w Z R c d O) (R + O.length + 1) (some (.out o)) =
      TTw w Z R c d (O ++ [o]) := by
  funext i
  by_cases hi : i = R + O.length + 1
  · subst hi
    rw [Function.update_self]
    unfold TTw TT
    have hR : ¬ R + O.length + 1 ≤ R := by omega
    have hk : (R + O.length + 1 - R - 1).toNat = O.length := by omega
    cases w <;> simp only [if_neg hR, if_true, if_neg Bool.false_ne_true] <;> simp [hk]
  · rw [Function.update_of_ne hi]
    unfold TTw TT
    by_cases hR : i ≤ R
    · cases w <;> simp only [if_pos hR, if_true, if_neg Bool.false_ne_true]
    · cases w <;> simp only [if_neg hR, if_true, if_neg Bool.false_ne_true] <;>
      by_cases hk : (i - R - 1).toNat < O.length
      all_goals first
        | (rw [List.getElem?_append_left hk])
        | (have h1 : O.length < (i - R - 1).toNat := by omega
           rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)])

theorem TTw_advance (hZ : ∀ i, lo ≤ i → i ≤ R → IsW0 (Z i)) (w : Bool) (c d : ℤ) (O)
    (hc : lo ≤ c) (hcR : c + 1 ≤ R) :
    Function.update (Function.update (TTw w Z R c d O) c (setFlag w (TTw w Z R c d O c) false))
      (c + 1) (setFlag w (Function.update (TTw w Z R c d O) c
        (setFlag w (TTw w Z R c d O c) false) (c + 1)) true) = TTw w Z R (c + 1) d O := by
  have e1 : Function.update (TTw w Z R c d O) c (setFlag w (TTw w Z R c d O c) false) (c + 1) =
      TTw w Z R c d O (c + 1) := Function.update_of_ne (by omega) _ _
  rw [e1]
  have hc1 : c ≤ R := by omega
  have hZc := hZ c hc hc1
  have hZc1 := hZ (c + 1) (by omega) hcR
  funext i
  by_cases h1 : i = c + 1
  · subst h1
    rw [Function.update_self]
    unfold TTw TT
    cases w
    · simp only [if_neg Bool.false_ne_true, if_pos hcR]
      rw [setFlag_false_flags _ hZc1]; simp
    · simp only [if_true, if_pos hcR]
      rw [setFlag_true_flags _ hZc1]; simp
  · rw [Function.update_of_ne h1]
    by_cases h2 : i = c
    · subst h2
      rw [Function.update_self]
      unfold TTw TT
      cases w
      · simp only [if_neg Bool.false_ne_true, if_pos hc1]
        rw [setFlag_false_flags _ hZc]; simp
      · simp only [if_true, if_pos hc1]
        rw [setFlag_true_flags _ hZc]; simp
    · rw [Function.update_of_ne h2]
      unfold TTw TT
      cases w <;> simp only [if_true, if_neg Bool.false_ne_true] <;> split_ifs <;> simp [h1, h2]

/-- Walking right to the end of the tape and appending the output cell `o`. -/
theorem carry_end (hZ : ∀ i, lo ≤ i → i ≤ R → IsW0 (Z i)) (w w' : Bool) (o : Option (B ⊕ C))
    (c d : ℤ) (O) (q0 : ℤ) (hq0 : lo ≤ q0) (hq0' : q0 ≤ R + O.length + 1)
    (cfg : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q)
    (h : Rel (CM ιfo ιgo Mf Mg) cfg (.carry w' o) (TTw w Z R c d O) q0) :
    Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run ((R + O.length + 1 - q0).toNat + 1) cfg)
      (.find w') (TTw w Z R c d (O ++ [o])) (R + O.length) := by
  have h1 := sweep_right_to (CM ιfo ιgo Mf Mg) (.carry w' o) (nh _ _ _ _ (by simp) (by simp))
    (fun s => s.isSome = true) (fun s hs => d_carry_some ιfo ιgo Mf Mg w' o s hs) cfg _ q0
    (R + O.length + 1) h hq0' (fun i hi1 hi2 => TTw_isSome hZ w c d O i (by omega) (by omega))
  have h2 := step_rel (CM ιfo ιgo Mf Mg) h1 (nh _ _ _ _ (by simp) (by simp))
    (show (CM ιfo ιgo Mf Mg).δ (.carry w' o) (TTw w Z R c d O (R + O.length + 1)) =
      (.find w', some (.out o), .left) by rw [TTw_end]; rfl)
  rw [run_add, run_one]
  rw [TTw_append] at h2
  exact h2.congrP _ (by simp [mv])

/-- One transport iteration. -/
theorem iter (hZ : ∀ i, lo ≤ i → i ≤ R → IsW0 (Z i)) (w : Bool) (c d : ℤ) (O) (p : ℤ)
    (o : B ⊕ C) (hc : lo ≤ c) (hcR : c + 1 ≤ R) (hcp : c ≤ p) (hp : p ≤ R + O.length)
    (ho : trk ιfo ιgo w (Z c) = some o) (cfg : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q)
    (h : Rel (CM ιfo ιgo Mf Mg) cfg (.find w) (TTw w Z R c d O) p) :
    Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run
      ((p - c).toNat + (1 + (1 + ((R + O.length + 1 - (c + 2)).toNat + 1)))) cfg)
      (.find w) (TTw w Z R (c + 1) d (O ++ [some o])) (R + O.length) := by
  have h1 := sweep_left_to (CM ιfo ιgo Mf Mg) (.find w) (nh _ _ _ _ (by simp) (by simp))
    (fun s => flag w s = false) (fun s hs => d_find_no ιfo ιgo Mf Mg w s hs) cfg _ p c h hcp
    (fun i hi1 hi2 => TTw_flag_ne hZ w c d O i (by omega) (by omega))
  have hfc := TTw_flag_c hZ w c d O hc (by omega)
  have htc : trk ιfo ιgo w (TTw w Z R c d O c) = some o := by
    rw [TTw_trk ιfo ιgo w c d O c (by omega)]; exact ho
  have h2 := step_rel (CM ιfo ιgo Mf Mg) h1 (nh _ _ _ _ (by simp) (by simp))
    (d_find_some ιfo ιgo Mf Mg w _ hfc o htc)
  rw [show c + mv Move.right = c + 1 from rfl] at h2
  have h3 := step_rel (CM ιfo ιgo Mf Mg) h2 (nh _ _ _ _ (by simp) (by simp))
    (d_mark ιfo ιgo Mf Mg w o _)
  rw [TTw_advance hZ w c d O hc hcR] at h3
  have h4 := carry_end ιfo ιgo Mf Mg hZ w w (some o) (c + 1) d O (c + 1 + mv Move.right)
    (by simp [mv]; omega) (by simp [mv]; omega) _ h3
  rw [show c + 1 + mv Move.right = c + 2 by simp [mv]; ring] at h4
  rw [run_add, run_add, run_one, run_add, run_one]
  exact h4

theorem loop (hZ : ∀ i, lo ≤ i → i ≤ R → IsW0 (Z i)) (w : Bool) (d : ℤ) (S : List (B ⊕ C))
    (c0 : ℤ) (hc0 : lo ≤ c0) (hS : c0 + S.length ≤ R)
    (htrk : ∀ j : ℕ, j < S.length → trk ιfo ιgo w (Z (c0 + j)) = S[j]?) (D : ℕ) :
    ∀ k j : ℕ, j + k = S.length → ∀ (O : List (Option (B ⊕ C))) (p : ℤ)
      (cfg : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q),
      c0 + j ≤ p → p ≤ R + O.length → R + O.length + k - lo ≤ D →
      Rel (CM ιfo ιgo Mf Mg) cfg (.find w) (TTw w Z R (c0 + j) d O) p →
      ∃ t p', t ≤ k * (2 * D + 3) ∧ c0 + S.length ≤ p' ∧ p' ≤ R + O.length + k ∧
        Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run t cfg) (.find w)
          (TTw w Z R (c0 + S.length) d (O ++ (S.drop j).map some)) p' := by
  intro k
  induction k with
  | zero =>
    intro j hj O p cfg h1 h2 h3 h
    have hj' : j = S.length := by omega
    subst hj'
    refine ⟨0, p, by simp, by omega, by omega, ?_⟩
    rw [run_zero]; simpa using h
  | succ k ih =>
    intro j hj O p cfg h1 h2 h3 h
    have hjS : j < S.length := by omega
    have ho : trk ιfo ιgo w (Z (c0 + j)) = some S[j] := by
      rw [htrk j hjS, List.getElem?_eq_getElem hjS]
    have hi := iter ιfo ιgo Mf Mg hZ w (c0 + j) d O p S[j] (by omega) (by omega) h1 h2 ho cfg h
    obtain ⟨t, p', ht, hp1, hp2, hr⟩ := ih (j + 1) (by omega) (O ++ [some S[j]]) (R + O.length) _
      (by push_cast; omega) (by simp) (by simp; omega)
      (by rw [show c0 + ((j + 1 : ℕ) : ℤ) = c0 + j + 1 by push_cast; ring]; exact hi)
    have hle : (p - (c0 + j)).toNat + (1 + (1 + ((R + O.length + 1 - (c0 + j + 2)).toNat + 1))) ≤
        2 * D + 3 := by push_cast at h3; omega
    refine ⟨(p - (c0 + j)).toNat + (1 + (1 + ((R + O.length + 1 - (c0 + j + 2)).toNat + 1))) + t,
      p', ?_, hp1, ?_, ?_⟩
    · calc _ ≤ (2 * D + 3) + k * (2 * D + 3) := by omega
        _ = (k + 1) * (2 * D + 3) := by ring
    · simp at hp2; push_cast; omega
    · have e : O ++ [some S[j]] ++ (S.drop (j + 1)).map some = O ++ (S.drop j).map some := by
        rw [List.drop_eq_getElem_cons hjS, List.map_cons, List.append_assoc, List.singleton_append]
      rw [run_add, ← e]; exact hr

/-- The end of a transport: the cursor reaches the blank of its track. -/
theorem done (hZ : ∀ i, lo ≤ i → i ≤ R → IsW0 (Z i)) (w : Bool) (c d : ℤ) (O) (p : ℤ)
    (hc : lo ≤ c) (hcR : c ≤ R) (hcp : c ≤ p) (ho : trk ιfo ιgo w (Z c) = none)
    (cfg : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q)
    (h : Rel (CM ιfo ιgo Mf Mg) cfg (.find w) (TTw w Z R c d O) p) :
    Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run ((p - c).toNat + 1) cfg)
      (if w then .goEndFin else .carry true none) (TTw w Z R c d O) (c + 1) := by
  have h1 := sweep_left_to (CM ιfo ιgo Mf Mg) (.find w) (nh _ _ _ _ (by simp) (by simp))
    (fun s => flag w s = false) (fun s hs => d_find_no ιfo ιgo Mf Mg w s hs) cfg _ p c h hcp
    (fun i hi1 hi2 => TTw_flag_ne hZ w c d O i (by omega) (by omega))
  have hfc := TTw_flag_c hZ w c d O hc hcR
  have htc : trk ιfo ιgo w (TTw w Z R c d O c) = none := by
    rw [TTw_trk ιfo ιgo w c d O c hcR]; exact ho
  have h2 := step_rel_keep (CM ιfo ιgo Mf Mg) h1 (nh _ _ _ _ (by simp) (by simp))
    (d_find_none ιfo ιgo Mf Mg w _ hfc htc)
  rw [run_add, run_one]
  exact h2

/-- The final phase: walk to the end, walk back over the output, stop on its first cell. -/
theorem final (hZ : ∀ i, lo ≤ i → i ≤ R → IsW0 (Z i)) (cf cg : ℤ) (O) (hc : lo ≤ cg)
    (hcR : cg ≤ R) (cfg : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q)
    (h : Rel (CM ιfo ιgo Mf Mg) cfg .goEndFin (TTw true Z R cg cf O) (cg + 1)) :
    Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run
      ((R + O.length + 1 - (cg + 1)).toNat + (1 + (O.length + 1))) cfg)
      .acc (TTw true Z R cg cf O) (R + 1) := by
  have h1 := sweep_right_to (CM ιfo ιgo Mf Mg) .goEndFin (nh _ _ _ _ (by simp) (by simp))
    (fun s => s.isSome = true) (fun s hs => d_goEndFin_some ιfo ιgo Mf Mg s hs) cfg _ (cg + 1)
    (R + O.length + 1) h (by omega)
    (fun i hi1 hi2 => TTw_isSome hZ true cg cf O i (by omega) (by omega))
  have h2 := step_rel_keep (CM ιfo ιgo Mf Mg) h1 (nh _ _ _ _ (by simp) (by simp))
    (show (CM ιfo ιgo Mf Mg).δ .goEndFin (TTw true Z R cg cf O (R + O.length + 1)) =
      (.backOut, TTw true Z R cg cf O (R + O.length + 1), .left) by rw [TTw_end]; rfl)
  rw [show R + O.length + 1 + mv Move.left = R + O.length by simp [mv]] at h2
  have h3 := sweep_left_to (CM ιfo ιgo Mf Mg) .backOut (nh _ _ _ _ (by simp) (by simp))
    (fun s => isOut s = true) (fun s hs => d_backOut_out ιfo ιgo Mf Mg s hs) _ _ _ R h2
    (by omega) (fun i hi1 hi2 => TTw_isOut true cg cf O i hi1 hi2)
  have hW : IsW (TTw true Z R cg cf O R) := by
    unfold TTw TT
    simp only [if_true, if_pos (le_refl R)]
    obtain ⟨a, b, o, he⟩ := hZ R (by omega) (le_refl R)
    rw [he]; exact ⟨_, _, _, _, _, rfl⟩
  have h4 := step_rel_keep (CM ιfo ιgo Mf Mg) h3 (nh _ _ _ _ (by simp) (by simp))
    (d_backOut_work ιfo ιgo Mf Mg _ hW)
  have e : (R + O.length - R).toNat = O.length := by omega
  rw [e] at h4
  simp only [run_add, run_one]
  exact h4.congrP _ (by simp [mv])

theorem final_output (cf cg : ℤ) (O : List (Option (B ⊕ C)))
    (cfg : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q)
    (h : Rel (CM ιfo ιgo Mf Mg) cfg .acc (TTw true Z R cg cf O) (R + 1)) :
    (CM ιfo ιgo Mf Mg).output cfg = (O.map Sym.out).map some := by
  apply output_of_rel _ h
  intro n
  unfold TTw TT
  have hR : ¬ R + 1 + n ≤ R := by omega
  have hk : (R + 1 + n - R - 1).toNat = n := by omega
  simp only [if_true, if_neg hR, hk, List.getElem?_map]

end Transport


section Front

variable {A Γf Γg B C : Type} [Fintype B] [Fintype C]
variable (ιfo : B ↪ Γf) (ιgo : C ↪ Γg) (Mf : TM Γf) (Mg : TM Γg)

def inEmb (ιfA : A ↪ Γf) (ιgA : A ↪ Γg) : A ↪ Sym Γf Γg B C :=
  ⟨fun a => .work (some (ιfA a)) (some (ιgA a)) false false false, by
    intro a b h
    injection h with h1
    exact ιfA.injective (Option.some.inj h1)⟩

theorem init_cases (ιfA : A ↪ Γf) (ιgA : A ↪ Γg) (x : List A) (i : ℤ) :
    (initTape (x.map (inEmb (B := B) (C := C) ιfA ιgA)) i = none ∧
      initTape (x.map ιfA) i = none ∧ initTape (x.map ιgA) i = none) ∨
    ∃ a, initTape (x.map (inEmb (B := B) (C := C) ιfA ιgA)) i =
        some (.work (some (ιfA a)) (some (ιgA a)) false false false) ∧
      initTape (x.map ιfA) i = some (ιfA a) ∧ initTape (x.map ιgA) i = some (ιgA a) := by
  unfold initTape
  split_ifs with h0
  · simp only [List.getElem?_map]
    cases x[i.toNat]? with
    | none => left; simp
    | some a => right; exact ⟨a, rfl, rfl, rfl⟩
  · left; simp

theorem init_isSome (ιfA : A ↪ Γf) (ιgA : A ↪ Γg) (x : List A) (i : ℤ) :
    (initTape (x.map (inEmb (B := B) (C := C) ιfA ιgA)) i).isSome = true ↔
      (0 ≤ i ∧ i < x.length) := by
  unfold initTape
  split_ifs with h0
  · simp only [List.getElem?_map, Option.isSome_map]
    rcases lt_or_ge i.toNat x.length with h | h
    · simp [List.getElem?_eq_getElem h]; omega
    · simp [List.getElem?_eq_none h]; omega
  · simp; omega

theorem orgOf_setOrg (s : Option (Sym Γf Γg B C)) (hs : Pc s) : orgOf (setOrg s) = true := by
  rcases hs with rfl | ⟨a, b, o, f, g, rfl⟩ <;> rfl

theorem Pc_setOrg (s : Option (Sym Γf Γg B C)) (hs : Pc s) : Pc (setOrg s) := by
  right; rcases hs with rfl | ⟨a, b, o, f, g, rfl⟩ <;> exact ⟨_, _, _, _, _, rfl⟩

theorem not_isSome {α : Type} (o : Option α) (h : ¬ o.isSome = true) : o = none := by
  cases o
  · rfl
  · simp at h

/-- Setup and simulation of the first machine, followed by the return to the origin. -/
theorem phase1 (ιfA : A ↪ Γf) (ιgA : A ↪ Γg) (x : List A) (F : List B) (Nf : ℕ)
    (hf1 : Mf.HaltsWithin Nf (x.map ιfA))
    (hf2 : Mf.output (Mf.run Nf (Mf.init (x.map ιfA))) = F.map (some ∘ ιfo)) :
    ∃ (t n1 : ℕ) (T : ℤ → Option (Sym Γf Γg B C)) (h lo hi : ℤ),
      Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run t
        ((CM ιfo ιgo Mf Mg).init (x.map (inEmb ιfA ιgA)))) (.sim2 Mg.q₀) T 0 ∧
      Region T lo hi ∧ lo ≤ 0 ∧ 0 ≤ hi ∧ lo ≤ h ∧ h ≤ hi ∧ -(n1 : ℤ) ≤ lo ∧
      hi ≤ x.length + n1 ∧ n1 ≤ Nf ∧ t ≤ n1 + 2 * (hi - lo).toNat + 6 ∧
      (∀ i, Pc (T i)) ∧ (∀ i, tr2 (T i) = initTape (x.map ιgA) i) ∧
      (∀ i, flag false (T i) = decide (i = h)) ∧ (∀ i, flag true (T i) = false) ∧
      (∀ n : ℕ, tr1 (T (h + n)) = (F.map ιfo)[n]?) := by
  classical
  -- the setup
  set T0 := Function.update (initTape (x.map (inEmb (B := B) (C := C) ιfA ιgA))) 0
    (setOrg (initTape (x.map (inEmb (B := B) (C := C) ιfA ιgA)) 0)) with hT0
  have hPc00 : ∀ i, Pc ((initTape (x.map (inEmb (B := B) (C := C) ιfA ιgA))) i) := by
    intro i
    rcases init_cases (B := B) (C := C) ιfA ιgA x i with ⟨h1, -, -⟩ | ⟨a, h1, -, -⟩
    · left; exact h1
    · right; exact ⟨_, _, _, _, _, h1⟩
  have hs0 : Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run 2 ((CM ιfo ιgo Mf Mg).init (x.map (inEmb ιfA ιgA))))
      (.sim1 Mf.q₀) T0 0 := by
    have h0 := init_rel (CM ιfo ιgo Mf Mg) (x.map (inEmb ιfA ιgA))
    have h1 := step_rel (CM ιfo ιgo Mf Mg) h0 (nh _ _ _ _ (by intro h; cases h) (by intro h; cases h))
      (d_start ιfo ιgo Mf Mg _)
    have h2 := step_rel_keep (CM ιfo ιgo Mf Mg) h1 (nh _ _ _ _ (by simp) (by simp))
      (d_back0 ιfo ιgo Mf Mg _)
    exact h2.congrP _ (by simp [mv])
  have hT0tr1 : ∀ i, tr1 (T0 i) = initTape (x.map ιfA) i := by
    intro i
    rcases init_cases (B := B) (C := C) ιfA ιgA x i with ⟨h1, h2, -⟩ | ⟨a, h1, h2, -⟩
    · by_cases hi : i = 0
      · subst hi; rw [hT0, Function.update_self, tr1_setOrg, h2, h1]; rfl
      · rw [hT0, Function.update_of_ne hi, h2, h1]; rfl
    · by_cases hi : i = 0
      · subst hi; rw [hT0, Function.update_self, tr1_setOrg, h2, h1]; rfl
      · rw [hT0, Function.update_of_ne hi, h2, h1]; rfl
  have hT0tr2 : ∀ i, tr2 (T0 i) = initTape (x.map ιgA) i := by
    intro i
    rcases init_cases (B := B) (C := C) ιfA ιgA x i with ⟨h1, -, h2⟩ | ⟨a, h1, -, h2⟩
    · by_cases hi : i = 0
      · subst hi; rw [hT0, Function.update_self, tr2_setOrg, h2, h1]; rfl
      · rw [hT0, Function.update_of_ne hi, h2, h1]; rfl
    · by_cases hi : i = 0
      · subst hi; rw [hT0, Function.update_self, tr2_setOrg, h2, h1]; rfl
      · rw [hT0, Function.update_of_ne hi, h2, h1]; rfl
  have hT0org : ∀ i, orgOf (T0 i) = decide (i = 0) := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [hT0, Function.update_self, orgOf_setOrg _ (hPc00 0)]; rfl
    · rw [hT0, Function.update_of_ne hi]
      rcases init_cases (B := B) (C := C) ιfA ιgA x i with ⟨h1, -, -⟩ | ⟨a, h1, -, -⟩
      · rw [h1]; simp [hi]; rfl
      · rw [h1]; simp [hi]; rfl
  have hT0flag : ∀ w' i, flag w' (T0 i) = false := by
    intro w' i
    by_cases hi : i = 0
    · subst hi; rw [hT0, Function.update_self, flag_setOrg]
      rcases init_cases (B := B) (C := C) ιfA ιgA x 0 with ⟨h1, -, -⟩ | ⟨a, h1, -, -⟩
      · rw [h1]; cases w' <;> rfl
      · rw [h1]; cases w' <;> rfl
    · rw [hT0, Function.update_of_ne hi]
      rcases init_cases (B := B) (C := C) ιfA ιgA x i with ⟨h1, -, -⟩ | ⟨a, h1, -, -⟩
      · rw [h1]; cases w' <;> rfl
      · rw [h1]; cases w' <;> rfl
  have hT0Pc : ∀ i, Pc (T0 i) := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [hT0, Function.update_self]; exact Pc_setOrg _ (hPc00 0)
    · rw [hT0, Function.update_of_ne hi]; exact hPc00 i
  set H0 : ℤ := max ((x.length : ℤ) - 1) 0 with hH0
  have hReg0 : Region T0 0 H0 := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [hT0, Function.update_self]; simp [setOrg]; omega
    · rw [hT0, Function.update_of_ne hi, init_isSome]; omega
  -- the simulation of the first machine
  have hex : ∃ n, Halt Mf (Mf.run n (Mf.init (x.map ιfA))).state := ⟨Nf, hf1⟩
  set n1 := Nat.find hex with hn1
  have hn1H : Halt Mf (Mf.run n1 (Mf.init (x.map ιfA))).state := Nat.find_spec hex
  have hn1le : n1 ≤ Nf := Nat.find_min' hex hf1
  have hsim := simulate (CM ιfo ιgo Mf Mg) Mf (fun q => .sim1 q) tr1 set1 tr1_set1
    (fun q => nh _ _ _ _ (by simp) (by simp)) (fun q s hq => d_sim1 ιfo ιgo Mf Mg q hq s)
    (InvS er1 Pc T0 0 H0)
    (fun k T p w d hI => InvS_step er1 Pc T0 0 H0 le_rfl (by omega) set1 set1_isSome er1_set1
      Pc_set1 k T p w d hI)
  obtain ⟨T1, h, r1, r2, r3⟩ := hsim n1 0 _ (Mf.init (x.map ιfA)) T0 0 hs0
    ((init_rel Mf _).congrT _ (funext fun i => (hT0tr1 i).symm))
    ⟨⟨0, H0, hReg0, by omega, by omega, by simp, le_rfl, le_rfl, by simp⟩, fun i => rfl,
      by simp, by simp, hT0Pc⟩
    (fun m hm => Nat.find_min hex hm)
  have hout : Mf.output (Mf.run n1 (Mf.init (x.map ιfA))) = (F.map ιfo).map some := by
    rw [← run_mono Mf _ hn1H hn1le, hf2, List.map_map]
  have htr1 := tape_of_output Mf r2 (F.map ιfo) hout
  obtain ⟨⟨lo, hi, hReg1, hlo1, hhi1, hL1, hL1', hH1, hH1'⟩, her, hp1, hp2, hpc⟩ := r3
  -- the halting step
  have s1 := step_rel (CM ιfo ιgo Mf Mg) r1 (nh _ _ _ _ (by simp) (by simp))
    (d_sim1_halt ιfo ιgo Mf Mg _ hn1H (T1 h))
  set T := Function.update T1 h (setFlag false (T1 h) true) with hT
  have hRegT : Region T (min lo h) (max hi h) := by
    intro i
    by_cases hi' : i = h
    · subst hi'; rw [hT, Function.update_self]; simp [setFlag_isSome]
    · rw [hT, Function.update_of_ne hi', hReg1 i]; omega
  have s2 := sweep_right_to (CM ιfo ιgo Mf Mg) .goEnd1 (nh _ _ _ _ (by simp) (by simp))
    (fun s => s.isSome = true) (fun s hs => d_goEnd1_some ιfo ιgo Mf Mg s hs) _ T (h + 1)
    (max hi h + 1) (s1.congrP _ (by simp [mv])) (by omega)
    (fun i hi1 hi2 => (hRegT i).2 ⟨by omega, by omega⟩)
  have hnone : T (max hi h + 1) = none := not_isSome _ (fun hc => by have := (hRegT _).1 hc; omega)
  have s3 := step_rel_keep (CM ιfo ιgo Mf Mg) s2 (nh _ _ _ _ (by simp) (by simp))
    (show (CM ιfo ιgo Mf Mg).δ .goEnd1 (T (max hi h + 1)) = (.findOrg, T (max hi h + 1), .left)
      by rw [hnone]; rfl)
  have horg : ∀ i, orgOf (T i) = decide (i = 0) := by
    intro i
    have e := congrArg orgOf (her i)
    rw [org_er1, org_er1, hT0org] at e
    by_cases hi' : i = h
    · subst hi'; rw [hT, Function.update_self, org_setFlag, e]
    · rw [hT, Function.update_of_ne hi', e]
  have s4 := sweep_left_to (CM ιfo ιgo Mf Mg) .findOrg (nh _ _ _ _ (by simp) (by simp))
    (fun s => orgOf s = false) (fun s hs => d_findOrg_no ιfo ιgo Mf Mg s hs) _ T (max hi h) 0
    (s3.congrP _ (show max hi h + 1 + mv Move.left = max hi h by simp [mv])) (by omega)
    (fun i hi1 hi2 => by rw [horg i]; simp; omega)
  have s5 := step_rel_keep (CM ιfo ιgo Mf Mg) s4 (nh _ _ _ _ (by simp) (by simp))
    (d_findOrg_yes ιfo ιgo Mf Mg (T 0) (by rw [horg 0]; rfl))
  have s6 := step_rel_keep (CM ιfo ιgo Mf Mg) s5 (nh _ _ _ _ (by simp) (by simp))
    (d_toSim2 ιfo ιgo Mf Mg _)
  refine ⟨2 + (n1 + (1 + ((max hi h + 1 - (h + 1)).toNat + (1 + ((max hi h - 0).toNat +
    (1 + 1)))))), n1, T, h, min lo h, max hi h, ?_, hRegT, by omega, by omega, by omega,
    by omega, by omega, by omega, hn1le, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [run_add, run_one]
    exact s6.congrP _ (show (0 : ℤ) + mv Move.left + mv Move.right = 0 by simp [mv])
  · intro i
    by_cases hi' : i = h
    · subst hi'; rw [hT, Function.update_self]; exact Pc_setFlag _ _ _ (hpc _)
    · rw [hT, Function.update_of_ne hi']; exact hpc i
  · intro i
    have e := congrArg tr2 (her i)
    rw [tr2_er1, tr2_er1, hT0tr2] at e
    by_cases hi' : i = h
    · subst hi'; rw [hT, Function.update_self, tr2_setFlag, e]
    · rw [hT, Function.update_of_ne hi', e]
  · intro i
    by_cases hi' : i = h
    · subst hi'; rw [hT, Function.update_self, flag_setFlag_self _ _ (hpc _)]; simp
    · rw [hT, Function.update_of_ne hi']
      have e := congrArg (flag false) (her i)
      rw [flag_er1, flag_er1, hT0flag] at e
      rw [e]; simp [hi']
  · intro i
    have e := congrArg (flag true) (her i)
    rw [flag_er1, flag_er1, hT0flag] at e
    by_cases hi' : i = h
    · subst hi'; rw [hT, Function.update_self, flag_true_setFlag_false, e]
    · rw [hT, Function.update_of_ne hi', e]
  · intro n
    by_cases hn : n = 0
    · subst hn
      have := htr1 0
      simp only [Nat.cast_zero, add_zero] at this ⊢
      rw [hT, Function.update_self, tr1_setFlag, this]
    · rw [hT, Function.update_of_ne (by omega)]
      exact htr1 n

/-- Simulation of the second machine and setup of the padded work region for transport. -/
theorem phase2_sim (ιgA : A ↪ Γg) (x : List A) (F : List B) (G : List C) (Nf Ng : ℕ)
    (n1 : ℕ) (T : ℤ → Option (Sym Γf Γg B C)) (h lo hi : ℤ)
    (cfg : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q)
    (hrel : Rel (CM ιfo ιgo Mf Mg) cfg (.sim2 Mg.q₀) T 0)
    (hReg : Region T lo hi) (hlo0 : lo ≤ 0) (h0hi : 0 ≤ hi)
    (hloh : lo ≤ h) (hhhi : h ≤ hi) (hlo_n1 : -(n1 : ℤ) ≤ lo)
    (hhi_n1 : hi ≤ x.length + n1) (hn1 : n1 ≤ Nf)
    (hPc : ∀ i, Pc (T i)) (htr2_init : ∀ i, tr2 (T i) = initTape (x.map ιgA) i)
    (hflagF : ∀ i, flag false (T i) = decide (i = h))
    (hflagT : ∀ i, flag true (T i) = false)
    (htr1_F : ∀ n : ℕ, tr1 (T (h + n)) = (F.map ιfo)[n]?)
    (hg1 : Mg.HaltsWithin Ng (x.map ιgA))
    (hg2 : Mg.output (Mg.run Ng (Mg.init (x.map ιgA))) = G.map (some ∘ ιgo)) :
    ∃ (t0 : ℕ) (Z : ℤ → Option (Sym Γf Γg B C)) (lo3 R h2 : ℤ),
      let M := x.length + 2 * Nf + 2 * Ng + 1
      Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run t0 cfg) (.find false)
        (TTw false Z R h h2 []) (R - 1) ∧
      (∀ i, lo3 ≤ i → i ≤ R → IsW0 (Z i)) ∧
      lo3 ≤ h ∧ h + F.length ≤ R ∧ lo3 ≤ h2 ∧ h2 + G.length ≤ R ∧
      h ≤ R - 1 ∧ h2 ≤ R - 1 ∧ (R - lo3).toNat ≤ M ∧ t0 ≤ 2 * M + 2 ∧
      (∀ j : ℕ, j < F.length → trk ιfo ιgo false (Z (h + j)) = (F.map (Sum.inl : B → B ⊕ C))[j]?) ∧
      trk ιfo ιgo false (Z (h + F.length)) = none ∧
      (∀ j : ℕ, j < G.length → trk ιfo ιgo true (Z (h2 + j)) = (G.map (Sum.inr : C → B ⊕ C))[j]?) ∧
      trk ιfo ιgo true (Z (h2 + G.length)) = none := by
  classical
  have hex : ∃ n, Halt Mg (Mg.run n (Mg.init (x.map ιgA))).state := ⟨Ng, hg1⟩
  set n2 := Nat.find hex with hn2
  have hn2H : Halt Mg (Mg.run n2 (Mg.init (x.map ιgA))).state := Nat.find_spec hex
  have hn2le : n2 ≤ Ng := Nat.find_min' hex hg1
  have hsim := simulate (CM ιfo ιgo Mf Mg) Mg (fun q => .sim2 q) tr2 set2 tr2_set2
    (fun q => nh _ _ _ _ (by simp) (by simp)) (fun q s hq => d_sim2 ιfo ιgo Mf Mg q hq s)
    (InvS er2 Pc T lo hi)
    (fun k T' p w d hI => InvS_step er2 Pc T lo hi hlo0 h0hi set2 set2_isSome er2_set2
      Pc_set2 k T' p w d hI)
  obtain ⟨T2, h2, r1, r2, r3⟩ := hsim n2 0 cfg (Mg.init (x.map ιgA)) T 0 hrel
    ((init_rel Mg _).congrT _ (funext fun i => (htr2_init i).symm))
    ⟨⟨lo, hi, hReg, by omega, by omega, by simp, le_rfl, le_rfl, by simp⟩, fun i => rfl,
      by simp, by simp, hPc⟩
    (fun m hm => Nat.find_min hex hm)
  have hout2 : Mg.output (Mg.run n2 (Mg.init (x.map ιgA))) = (G.map ιgo).map some := by
    rw [← run_mono Mg _ hn2H hn2le, hg2, List.map_map]
  have htr2 := tape_of_output Mg r2 (G.map ιgo) hout2
  obtain ⟨⟨lo2, hi2, hReg2, hlo2, hhi2, hL2, hL2', hH2, hH2'⟩, her2, hp2_1, hp2_2, hpc2⟩ := r3
  have s1 := step_rel (CM ιfo ιgo Mf Mg) r1 (nh _ _ _ _ (by simp) (by simp))
    (d_sim2_halt ιfo ιgo Mf Mg _ hn2H (T2 h2))
  set T3 := Function.update T2 h2 (setFlag true (T2 h2) true) with hT3
  set lo3 : ℤ := min lo2 h2 with hlo3
  set hi3 : ℤ := max hi2 h2 with hhi3
  have hReg3 : Region T3 lo3 hi3 := by
    intro i
    by_cases hi' : i = h2
    · subst hi'; rw [hT3, Function.update_self]; simp [setFlag_isSome]; omega
    · rw [hT3, Function.update_of_ne hi', hReg2 i]; omega
  have s2 := sweep_right_to (CM ιfo ιgo Mf Mg) .goEnd2 (nh _ _ _ _ (by simp) (by simp))
    (fun s => s.isSome = true) (fun s hs => d_goEnd2_some ιfo ιgo Mf Mg s hs) _ T3 (h2 + 1)
    (hi3 + 1) (s1.congrP _ (by simp [mv])) (by omega)
    (fun i hi1 hi2 => (hReg3 i).2 ⟨by omega, by omega⟩)
  have hnone3 : T3 (hi3 + 1) = none :=
    not_isSome _ (fun hc => by have := (hReg3 _).1 hc; omega)
  have s3 := step_rel (CM ιfo ιgo Mf Mg) s2 (nh _ _ _ _ (by simp) (by simp))
    (show (CM ιfo ιgo Mf Mg).δ .goEnd2 (T3 (hi3 + 1)) = (.find false, pad, .left)
      by rw [hnone3]; rfl)
  set R : ℤ := hi3 + 1 with hR_def
  set T4 := Function.update T3 R pad with hT4
  have hReg4 : Region T4 lo3 R := by
    intro i
    by_cases hi' : i = R
    · subst hi'; rw [hT4, Function.update_self]; simp [pad]; omega
    · rw [hT4, Function.update_of_ne hi', hReg3 i]; omega
  have hPc4 : ∀ i, Pc (T4 i) := by
    intro i
    by_cases hi' : i = R
    · subst hi'; rw [hT4, Function.update_self]; right; exact ⟨_, _, _, _, _, rfl⟩
    · rw [hT4, Function.update_of_ne hi']
      by_cases hi2' : i = h2
      · subst hi2'; rw [hT3, Function.update_self]; exact Pc_setFlag _ _ _ (hpc2 _)
      · rw [hT3, Function.update_of_ne hi2']; exact hpc2 i
  have hIsW4 : ∀ i, lo3 ≤ i → i ≤ R → IsW (T4 i) := by
    intro i hi1 hi2
    rcases hPc4 i with hn | hw
    · have := (hReg4 i).2 ⟨hi1, hi2⟩; rw [hn] at this; simp at this
    · exact hw
  have hflagF4 : ∀ i, flag false (T4 i) = decide (i = h) := by
    intro i
    by_cases hi' : i = R
    · subst hi'; rw [hT4, Function.update_self]
      have hne : R ≠ h := by omega
      simp [hne]; rfl
    · rw [hT4, Function.update_of_ne hi']
      have e := congrArg (flag false) (her2 i)
      rw [flag_er2, flag_er2, hflagF] at e
      by_cases hi2' : i = h2
      · subst hi2'; rw [hT3, Function.update_self, flag_false_setFlag_true, e]
      · rw [hT3, Function.update_of_ne hi2', e]
  have hflagT4 : ∀ i, flag true (T4 i) = decide (i = h2) := by
    intro i
    by_cases hi' : i = R
    · subst hi'; rw [hT4, Function.update_self]
      have hne : R ≠ h2 := by omega
      simp [hne]; rfl
    · rw [hT4, Function.update_of_ne hi']
      by_cases hi2' : i = h2
      · subst hi2'; rw [hT3, Function.update_self, flag_setFlag_self _ _ (hpc2 _)]; simp
      · rw [hT3, Function.update_of_ne hi2']
        have e := congrArg (flag true) (her2 i)
        rw [flag_er2, flag_er2, hflagT] at e
        rw [e]; simp [hi2']
  set Z : ℤ → Option (Sym Γf Γg B C) := fun i => flags (T4 i) false false with hZ_def
  have hZ : ∀ i, lo3 ≤ i → i ≤ R → IsW0 (Z i) :=
    fun i hi1 hi2 => IsW0_flags _ (hIsW4 i hi1 hi2)
  have hT4_eq : T4 = TTw false Z R h h2 [] := by
    funext i
    unfold TTw TT
    simp only [if_neg Bool.false_ne_true]
    by_cases hR : i ≤ R
    · rw [if_pos hR]
      by_cases hlo : lo3 ≤ i
      · rw [← hflagF4 i, ← hflagT4 i, hZ_def, flags_flags _ (hIsW4 i hlo hR)]
      · have hn : T4 i = none := not_isSome _ (fun hc => by have := (hReg4 i).1 hc; omega)
        simp only [hZ_def, hn]; rfl
    · rw [if_neg hR]
      have hn : T4 i = none := not_isSome _ (fun hc => by have := (hReg4 i).1 hc; omega)
      rw [hn]; rfl
  have htr1_T4 : ∀ i, i < R → tr1 (T4 i) = tr1 (T i) := by
    intro i hi'
    rw [hT4, Function.update_of_ne (by omega)]
    have e := congrArg tr1 (her2 i)
    rw [tr1_er2, tr1_er2] at e
    by_cases hi2' : i = h2
    · subst hi2'; rw [hT3, Function.update_self, tr1_setFlag, e]
    · rw [hT3, Function.update_of_ne hi2', e]
  have htr2_T4 : ∀ i, i < R → tr2 (T4 i) = tr2 (T2 i) := by
    intro i hi'
    rw [hT4, Function.update_of_ne (by omega)]
    by_cases hi2' : i = h2
    · subst hi2'; rw [hT3, Function.update_self, tr2_setFlag]
    · rw [hT3, Function.update_of_ne hi2']
  have hF_bound : h + F.length ≤ R := by
    rcases Nat.eq_zero_or_pos F.length with h0 | hpos
    · rw [h0]; omega
    · have hj : F.length - 1 < F.length := by omega
      have h1 := htr1_F (F.length - 1)
      rw [List.getElem?_map, List.getElem?_eq_getElem hj] at h1
      have hsome : (T (h + ((F.length - 1 : ℕ) : ℤ))).isSome = true := by
        cases hT' : T (h + ((F.length - 1 : ℕ) : ℤ))
        · rw [hT'] at h1; cases h1
        · rfl
      have := (hReg _).1 hsome
      omega
  have hG_bound : h2 + G.length ≤ R := by
    rcases Nat.eq_zero_or_pos G.length with h0 | hpos
    · rw [h0]; omega
    · have hj : G.length - 1 < G.length := by omega
      have h1 := htr2 (G.length - 1)
      rw [List.getElem?_map, List.getElem?_eq_getElem hj] at h1
      have hsome : (T2 (h2 + ((G.length - 1 : ℕ) : ℤ))).isSome = true := by
        cases hT' : T2 (h2 + ((G.length - 1 : ℕ) : ℤ))
        · rw [hT'] at h1; cases h1
        · rfl
      have := (hReg2 _).1 hsome
      omega
  have htrkF : ∀ j : ℕ, j < F.length →
      trk ιfo ιgo false (Z (h + j)) = (F.map (Sum.inl : B → B ⊕ C))[j]? := by
    intro j hj
    rw [hZ_def, trk_flags, trk]
    simp only [if_neg Bool.false_ne_true]
    rw [htr1_T4 (h + j) (by omega), htr1_F j]
    simp [List.getElem?_eq_getElem hj, dec_emb]
  have htrkF_end : trk ιfo ιgo false (Z (h + F.length)) = none := by
    rw [hZ_def, trk_flags, trk]
    simp only [if_neg Bool.false_ne_true]
    by_cases hlt : h + (F.length : ℤ) < R
    · rw [htr1_T4 _ hlt, htr1_F]
      have : (F.map ιfo)[F.length]? = none := by simp
      rw [this]; rfl
    · have heq : h + (F.length : ℤ) = R := by omega
      rw [heq, hT4, Function.update_self]; rfl
  have htrkG : ∀ j : ℕ, j < G.length →
      trk ιfo ιgo true (Z (h2 + j)) = (G.map (Sum.inr : C → B ⊕ C))[j]? := by
    intro j hj
    rw [hZ_def, trk_flags, trk]
    simp only [if_true]
    rw [htr2_T4 (h2 + j) (by omega), htr2 j]
    simp [List.getElem?_eq_getElem hj, dec_emb]
  have htrkG_end : trk ιfo ιgo true (Z (h2 + G.length)) = none := by
    rw [hZ_def, trk_flags, trk]
    simp only [if_true]
    by_cases hlt : h2 + (G.length : ℤ) < R
    · rw [htr2_T4 _ hlt, htr2]
      have : (G.map ιgo)[G.length]? = none := by simp
      rw [this]; rfl
    · have heq : h2 + (G.length : ℤ) = R := by omega
      rw [heq, hT4, Function.update_self]; rfl
  refine ⟨n2 + (1 + ((hi3 + 1 - (h2 + 1)).toNat + 1)), Z, lo3, R, h2, ?_, hZ,
    by omega, hF_bound, by omega, hG_bound, by omega, by omega, by omega, by omega,
    htrkF, htrkF_end, htrkG, htrkG_end⟩
  rw [run_add, run_add, run_one, run_add, run_one]
  exact (s3.congrT _ hT4_eq).congrP _ (by simp [mv, hR_def])

/-- Transport both outputs and finalize into `.acc`. -/
theorem phase2_transport (F : List B) (G : List C) (M : ℕ)
    (Z : ℤ → Option (Sym Γf Γg B C)) (lo3 R h h2 : ℤ)
    (cfg : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q)
    (hrel : Rel (CM ιfo ιgo Mf Mg) cfg (.find false) (TTw false Z R h h2 []) (R - 1))
    (hZ : ∀ i, lo3 ≤ i → i ≤ R → IsW0 (Z i))
    (hlo_h : lo3 ≤ h) (hF_bound : h + F.length ≤ R)
    (hlo_h2 : lo3 ≤ h2) (hG_bound : h2 + G.length ≤ R)
    (hhR : h ≤ R - 1) (hh2R : h2 ≤ R - 1) (hW_le : (R - lo3).toNat ≤ M)
    (htrkF : ∀ j : ℕ, j < F.length →
      trk ιfo ιgo false (Z (h + j)) = (F.map (Sum.inl : B → B ⊕ C))[j]?)
    (htrkF_end : trk ιfo ιgo false (Z (h + F.length)) = none)
    (htrkG : ∀ j : ℕ, j < G.length →
      trk ιfo ιgo true (Z (h2 + j)) = (G.map (Sum.inr : C → B ⊕ C))[j]?)
    (htrkG_end : trk ιfo ιgo true (Z (h2 + G.length)) = none) :
    ∃ t : ℕ,
      t ≤ 18 * M * M + 38 * M + 18 ∧
      (CM ιfo ιgo Mf Mg).IsHalting ((CM ιfo ιgo Mf Mg).run t cfg) ∧
      (CM ιfo ιgo Mf Mg).output ((CM ιfo ιgo Mf Mg).run t cfg) =
        ((F.map (some ∘ Sum.inl) ++ none :: G.map (some ∘ Sum.inr)).map Sym.out).map some := by
  set SF : List (B ⊕ C) := F.map Sum.inl with hSF
  set SG : List (B ⊕ C) := G.map Sum.inr with hSG
  have hSF_len : SF.length = F.length := by simp [hSF]
  have hSG_len : SG.length = G.length := by simp [hSG]
  set W := (R - lo3).toNat with hW_def
  set D1 := W + F.length with hD1
  obtain ⟨tL1, p1, htL1, hp1_lo, hp1_hi, hrL1⟩ :=
    loop ιfo ιgo Mf Mg hZ false h2 SF h hlo_h (by rw [hSF_len]; exact hF_bound)
      (fun j hj => htrkF j (by rwa [← hSF_len])) D1
      SF.length 0 (by omega) [] (R - 1) cfg
      (by omega) (by simp) (by simp [hD1, hW_def, hSF_len]; omega)
      (by simpa using hrel)
  set O1 : List (Option (B ⊕ C)) := SF.map some with hO1
  have hrL1' : Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run tL1 cfg) (.find false)
      (TTw false Z R (h + SF.length) h2 O1) p1 := by
    simpa [hO1] using hrL1
  set tD1 := (p1 - (h + SF.length)).toNat + 1 with htD1
  have hrD1 := done ιfo ιgo Mf Mg hZ false (h + SF.length) h2 O1 p1 (by omega)
    (by rw [hSF_len]; exact hF_bound) hp1_lo (by rw [hSF_len]; exact htrkF_end) _ hrL1'
  have hrD1' : Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run (tL1 + tD1) cfg) (.carry true none)
      (TTw false Z R (h + SF.length) h2 O1) (h + SF.length + 1) := by
    rw [run_add]; exact hrD1
  set tC1 := (R + O1.length + 1 - (h + SF.length + 1)).toNat + 1 with htC1
  have hrC1 := carry_end ιfo ιgo Mf Mg hZ false true none (h + SF.length) h2 O1
    (h + SF.length + 1) (by omega) (by simp [hO1, hSF_len]; omega) _ hrD1'
  set O2 : List (Option (B ⊕ C)) := O1 ++ [none] with hO2
  have hrC1' : Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run (tL1 + tD1 + tC1) cfg) (.find true)
      (TTw true Z R h2 (h + SF.length) O2) (R + O1.length) := by
    rw [run_add]; exact hrC1
  set D2 := W + O2.length + G.length with hD2
  obtain ⟨tL2, p2, htL2, hp2_lo, hp2_hi, hrL2⟩ :=
    loop ιfo ιgo Mf Mg hZ true (h + SF.length) SG h2 hlo_h2 (by rw [hSG_len]; exact hG_bound)
      (fun j hj => htrkG j (by rwa [← hSG_len])) D2
      SG.length 0 (by omega) O2 (R + O1.length) _
      (by omega) (by simp [hO2]) (by simp [hD2, hW_def, hSG_len]; omega)
      (by simpa using hrC1')
  set O3 : List (Option (B ⊕ C)) := O2 ++ SG.map some with hO3
  have hrL2' : Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run (tL1 + tD1 + tC1 + tL2) cfg) (.find true)
      (TTw true Z R (h2 + SG.length) (h + SF.length) O3) p2 := by
    rw [run_add]; simpa [hO3] using hrL2
  set tD2 := (p2 - (h2 + SG.length)).toNat + 1 with htD2
  have hrD2 := done ιfo ιgo Mf Mg hZ true (h2 + SG.length) (h + SF.length) O3 p2 (by omega)
    (by rw [hSG_len]; exact hG_bound) hp2_lo (by rw [hSG_len]; exact htrkG_end) _ hrL2'
  have hrD2' : Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run (tL1 + tD1 + tC1 + tL2 + tD2) cfg)
      .goEndFin (TTw true Z R (h2 + SG.length) (h + SF.length) O3) (h2 + SG.length + 1) := by
    rw [run_add]; exact hrD2
  set tF := (R + O3.length + 1 - (h2 + SG.length + 1)).toNat + (1 + (O3.length + 1)) with htF
  have hrF := final ιfo ιgo Mf Mg hZ (h + SF.length) (h2 + SG.length) O3 (by omega)
    (by simp [hSG]; omega) _ hrD2'
  set tTot := tL1 + tD1 + tC1 + tL2 + tD2 + tF with htTot
  have hrTot : Rel (CM ιfo ιgo Mf Mg) ((CM ιfo ιgo Mf Mg).run tTot cfg) .acc
      (TTw true Z R (h2 + SG.length) (h + SF.length) O3) (R + 1) := by
    rw [htTot, run_add]; exact hrF
  have hF_le : F.length ≤ M := by omega
  have hG_le : G.length ≤ M := by omega
  have hO1_len : O1.length = F.length := by simp [hO1, hSF]
  have hO2_len : O2.length = F.length + 1 := by simp [hO2, hO1_len]
  have hO3_len : O3.length = F.length + 1 + G.length := by simp [hO3, hO2_len, hSG]
  have htL1_le : tL1 ≤ M * (4 * M + 3) := by
    have hSF_len : SF.length = F.length := by simp [hSF]
    rw [hSF_len] at htL1
    calc tL1 ≤ F.length * (2 * D1 + 3) := htL1
      _ ≤ M * (4 * M + 3) := Nat.mul_le_mul hF_le (by omega)
  have htD1_le : tD1 ≤ 2 * M + 1 := by
    simp only [hSF, List.length_map, List.length_nil, Nat.cast_zero, add_zero] at htD1 hp1_hi; omega
  have htC1_le : tC1 ≤ 2 * M + 1 := by omega
  have htL2_le : tL2 ≤ M * (6 * M + 5) := by
    have hSG_len : SG.length = G.length := by simp [hSG]
    rw [hSG_len] at htL2
    calc tL2 ≤ G.length * (2 * D2 + 3) := htL2
      _ ≤ M * (6 * M + 5) := Nat.mul_le_mul hG_le (by omega)
  have htD2_le : tD2 ≤ 3 * M + 2 := by
    simp only [hSG, List.length_map] at htD2 hp2_hi; omega
  have htF_le : tF ≤ 5 * M + 4 := by omega
  have htTot_le : tTot ≤ 18 * M * M + 38 * M + 18 := by nlinarith
  refine ⟨tTot, htTot_le, Or.inl hrTot.1, ?_⟩
  have hout := final_output ιfo ιgo Mf Mg (h + SF.length) (h2 + SG.length) O3 _ hrTot
  have hO3_eq : O3 = F.map (some ∘ Sum.inl) ++ none :: G.map (some ∘ Sum.inr) := by
    simp [hO3, hO2, hO1, hSF, hSG, List.map_map, List.append_assoc]
  rw [hout, hO3_eq]

/-- Simulation of the second machine, transport of both outputs, and finalization. -/
theorem phase2 (ιgA : A ↪ Γg) (x : List A) (F : List B) (G : List C) (Nf Ng : ℕ)
    (n1 : ℕ) (T : ℤ → Option (Sym Γf Γg B C)) (h lo hi : ℤ)
    (cfg : Cfg (Sym Γf Γg B C) (CM ιfo ιgo Mf Mg).Q)
    (hrel : Rel (CM ιfo ιgo Mf Mg) cfg (.sim2 Mg.q₀) T 0)
    (hReg : Region T lo hi) (hlo0 : lo ≤ 0) (h0hi : 0 ≤ hi)
    (hloh : lo ≤ h) (hhhi : h ≤ hi) (hlo_n1 : -(n1 : ℤ) ≤ lo)
    (hhi_n1 : hi ≤ x.length + n1) (hn1 : n1 ≤ Nf)
    (hPc : ∀ i, Pc (T i)) (htr2_init : ∀ i, tr2 (T i) = initTape (x.map ιgA) i)
    (hflagF : ∀ i, flag false (T i) = decide (i = h))
    (hflagT : ∀ i, flag true (T i) = false)
    (htr1_F : ∀ n : ℕ, tr1 (T (h + n)) = (F.map ιfo)[n]?)
    (hg1 : Mg.HaltsWithin Ng (x.map ιgA))
    (hg2 : Mg.output (Mg.run Ng (Mg.init (x.map ιgA))) = G.map (some ∘ ιgo)) :
    ∃ t : ℕ,
      let M := x.length + 2 * Nf + 2 * Ng + 1
      t ≤ 20 * M * M + 40 * M + 20 ∧
      (CM ιfo ιgo Mf Mg).IsHalting ((CM ιfo ιgo Mf Mg).run t cfg) ∧
      (CM ιfo ιgo Mf Mg).output ((CM ιfo ιgo Mf Mg).run t cfg) =
        ((F.map (some ∘ Sum.inl) ++ none :: G.map (some ∘ Sum.inr)).map Sym.out).map some := by
  obtain ⟨t0, Z, lo3, R, h2, hrel0, hZ, hlo_h, hF_b, hlo_h2, hG_b, hhR, hh2R, hW_le, ht0_le,
    htrkF, htrkF_end, htrkG, htrkG_end⟩ :=
    phase2_sim ιfo ιgo Mf Mg ιgA x F G Nf Ng n1 T h lo hi cfg hrel hReg hlo0 h0hi hloh hhhi
      hlo_n1 hhi_n1 hn1 hPc htr2_init hflagF hflagT htr1_F hg1 hg2
  obtain ⟨t1, ht1_le, hhalt, hout⟩ :=
    phase2_transport ιfo ιgo Mf Mg F G (x.length + 2 * Nf + 2 * Ng + 1) Z lo3 R h h2 _ hrel0 hZ
      hlo_h hF_b hlo_h2 hG_b hhR hh2R hW_le htrkF htrkF_end htrkG htrkG_end
  refine ⟨t0 + t1, by nlinarith, ?_, ?_⟩
  · rw [run_add]; exact hhalt
  · rw [run_add]; exact hout

def outEmb {Γf Γg B C : Type} : Option (B ⊕ C) ↪ Sym Γf Γg B C :=
  ⟨Sym.out, fun _ _ h => Sym.out.inj h⟩

theorem poly_bound (c d : ℕ) : ∃ k : ℕ, ∀ n : ℕ, c * (n ^ d + 1) ≤ n ^ k + k := by
  refine ⟨d + 2 * c + 1, fun n => ?_⟩
  rcases n with _ | _ | n
  · have h0 : (0 : ℕ) ^ d ≤ 1 := by cases d <;> simp
    have h1 : (0 : ℕ) ^ (d + 2 * c + 1) = 0 := Nat.zero_pow (by omega)
    rw [h1, zero_add]
    calc c * (0 ^ d + 1) ≤ c * (1 + 1) := Nat.mul_le_mul_left c (Nat.add_le_add_right h0 1)
      _ ≤ d + 2 * c + 1 := by omega
  · simp; omega
  · have hn2 : 2 ≤ n + 2 := by omega
    have hpow1 : 1 ≤ (n + 2) ^ d := Nat.one_le_pow d (n + 2) (by omega)
    have h2c : 2 * c ≤ 2 ^ (2 * c) := Nat.le_of_lt (Nat.lt_two_pow_self)
    have hpow2 : 2 ^ (2 * c) ≤ (n + 2) ^ (2 * c) := Nat.pow_le_pow_left hn2 (2 * c)
    calc c * ((n + 2) ^ d + 1)
        ≤ c * ((n + 2) ^ d + (n + 2) ^ d) := Nat.mul_le_mul_left c (Nat.add_le_add_left hpow1 _)
      _ = (2 * c) * (n + 2) ^ d := by ring
      _ ≤ (n + 2) ^ (2 * c) * (n + 2) ^ d := Nat.mul_le_mul_right _ (le_trans h2c hpow2)
      _ = (n + 2) ^ (2 * c + d) := (Nat.pow_add (n + 2) (2 * c) d).symm
      _ ≤ (n + 2) ^ (d + 2 * c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ (n + 2) ^ (d + 2 * c + 1) + (d + 2 * c + 1) := Nat.le_add_right _ _

end Front


end CookPvsNP.TP

open CookPvsNP

theorem solution {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : List A → List B) (g : List A → List C)
    (hf : CookPvsNP.PolyTimeComputable f) (hg : CookPvsNP.PolyTimeComputable g) :
    CookPvsNP.PolyTimeComputable (fun x => (f x).map (some ∘ Sum.inl) ++ none :: (g x).map (some ∘ Sum.inr)) := by
  classical
  rcases hf with ⟨Γf, hΓf, ιfA, ιfo, Mf, kf, hf⟩
  rcases hg with ⟨Γg, hΓg, ιgA, ιgo, Mg, kg, hg⟩
  set d := max (max kf kg) 1 with hd_def
  set c1 := 7 + 2 * kf + 2 * kg with hc1_def
  set c2 := 400 * c1 * c1 with hc2_def
  obtain ⟨k, hk⟩ := TP.poly_bound c2 (2 * d)
  refine ⟨TP.Sym Γf Γg B C, inferInstance, TP.inEmb ιfA ιgA, TP.outEmb, TP.CM ιfo ιgo Mf Mg, k, ?_⟩
  intro x
  obtain ⟨hf1, hf2⟩ := hf x
  obtain ⟨hg1, hg2⟩ := hg x
  obtain ⟨t1, n1, T, h, lo, hi, hr1, hReg, hlo0, h0hi, hloh, hhhi, hlo_n1, hhi_n1, hn1, ht1,
    hPc, htr2, hflagF, hflagT, htr1⟩ := TP.phase1 ιfo ιgo Mf Mg ιfA ιgA x (f x)
    (x.length ^ kf + kf) hf1 hf2
  obtain ⟨t2, ht2, hhalt, hout⟩ := TP.phase2 ιfo ιgo Mf Mg ιgA x (f x) (g x)
    (x.length ^ kf + kf) (x.length ^ kg + kg) n1 T h lo hi _ hr1 hReg hlo0 h0hi hloh hhhi
    hlo_n1 hhi_n1 hn1 hPc htr2 hflagF hflagT htr1 hg1 hg2
  set M := x.length + 2 * (x.length ^ kf + kf) + 2 * (x.length ^ kg + kg) + 1 with hM_def
  have h1 : x.length ≤ x.length ^ d + 1 := by
    rcases x.length with _ | m
    · simp
    · calc m + 1 = (m + 1) ^ 1 := (Nat.pow_one _).symm
        _ ≤ (m + 1) ^ d := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ (m + 1) ^ d + 1 := Nat.le_add_right _ _
  have h2 : x.length ^ kf ≤ x.length ^ d + 1 := by
    rcases x.length with _ | m
    · cases kf <;> simp
    · exact le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.le_add_right _ _)
  have h3 : x.length ^ kg ≤ x.length ^ d + 1 := by
    rcases x.length with _ | m
    · cases kg <;> simp
    · exact le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.le_add_right _ _)
  have hM_le : M + 1 ≤ c1 * (x.length ^ d + 1) := by
    have : 1 ≤ x.length ^ d + 1 := by omega
    have hkf : kf ≤ kf * (x.length ^ d + 1) := Nat.le_mul_of_pos_right kf (by omega)
    have hkg : kg ≤ kg * (x.length ^ d + 1) := Nat.le_mul_of_pos_right kg (by omega)
    have : c1 * (x.length ^ d + 1) =
        7 * (x.length ^ d + 1) + 2 * (kf * (x.length ^ d + 1)) + 2 * (kg * (x.length ^ d + 1)) := by
      rw [hc1_def]; ring
    omega
  have ht1_le : t1 ≤ 3 * M + 6 := by
    have : (hi - lo).toNat ≤ M := by omega
    omega
  have htot_le : t1 + t2 ≤ x.length ^ k + k := by
    have hquad : t1 + t2 ≤ 100 * (M + 1) * (M + 1) := by nlinarith
    have hsq1 : (M + 1) * (M + 1) ≤ (c1 * (x.length ^ d + 1)) * (c1 * (x.length ^ d + 1)) :=
      Nat.mul_le_mul hM_le hM_le
    have hsq2 : (x.length ^ d + 1) * (x.length ^ d + 1) ≤ 4 * (x.length ^ (2 * d) + 1) := by
      have heq : x.length ^ (2 * d) = x.length ^ d * x.length ^ d := by
        rw [two_mul, Nat.pow_add]
      rw [heq]
      nlinarith
    have hmul : 100 * (M + 1) * (M + 1) ≤ c2 * (x.length ^ (2 * d) + 1) := by
      calc 100 * (M + 1) * (M + 1)
          = 100 * ((M + 1) * (M + 1)) := by ring
        _ ≤ 100 * ((c1 * (x.length ^ d + 1)) * (c1 * (x.length ^ d + 1))) :=
            Nat.mul_le_mul_left 100 hsq1
        _ = (100 * c1 * c1) * ((x.length ^ d + 1) * (x.length ^ d + 1)) := by ring
        _ ≤ (100 * c1 * c1) * (4 * (x.length ^ (2 * d) + 1)) :=
            Nat.mul_le_mul_left _ hsq2
        _ = c2 * (x.length ^ (2 * d) + 1) := by rw [hc2_def]; ring
    exact le_trans hquad (le_trans hmul (hk x.length))
  have hhalt' : (TP.CM ιfo ιgo Mf Mg).IsHalting
      ((TP.CM ιfo ιgo Mf Mg).run (t1 + t2) ((TP.CM ιfo ιgo Mf Mg).init (x.map (TP.inEmb ιfA ιgA)))) := by
    rw [TP.run_add]; exact hhalt
  have hrun_eq : (TP.CM ιfo ιgo Mf Mg).run (x.length ^ k + k)
      ((TP.CM ιfo ιgo Mf Mg).init (x.map (TP.inEmb ιfA ιgA))) =
      (TP.CM ιfo ιgo Mf Mg).run (t1 + t2)
      ((TP.CM ιfo ιgo Mf Mg).init (x.map (TP.inEmb ιfA ιgA))) :=
    TP.run_mono _ _ hhalt' htot_le
  refine ⟨?_, ?_⟩
  · unfold TM.HaltsWithin; rw [hrun_eq]; exact hhalt'
  · rw [hrun_eq, TP.run_add, hout, List.map_map]; rfl
