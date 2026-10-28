-- Prove2me | solution 1 for CookPvsNP.P_subset_NP
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:10:02.264809+00:00
-- url     : https://prove2.me/submissions/ee51ebac-0f13-4741-942a-bf8e64b24ebf

import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace CookPSubsetNP

open CookPvsNP

section generic

variable {Γ : Type} (M : TM Γ)

theorem run_succ (n : ℕ) (c : Cfg Γ M.Q) : M.run (n + 1) c = M.run n (M.step c) := by
  unfold TM.run; exact Function.iterate_succ_apply _ _ _

theorem run_succ' (n : ℕ) (c : Cfg Γ M.Q) : M.run (n + 1) c = M.step (M.run n c) := by
  unfold TM.run; exact Function.iterate_succ_apply' _ _ _

theorem run_add (a b : ℕ) (c : Cfg Γ M.Q) : M.run (a + b) c = M.run b (M.run a c) := by
  unfold TM.run; rw [Nat.add_comm]; exact Function.iterate_add_apply _ _ _ _

theorem step_halt (c : Cfg Γ M.Q) (h : M.IsHalting c) : M.step c = c := by
  unfold TM.step; rw [if_pos h]

theorem run_stable (c : Cfg Γ M.Q) (n : ℕ) (h : M.IsHalting (M.run n c)) :
    ∀ m, n ≤ m → M.run m c = M.run n c := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show n + (d + 1) = (n + d) + 1 from rfl, run_succ', ih (by omega), step_halt M _ h]

theorem accepts_iff (w : List Γ) (N : ℕ) (hN : M.HaltsWithin N w) :
    M.Accepts w ↔ (M.run N (M.init w)).state = M.qaccept := by
  constructor
  · rintro ⟨n, hn⟩
    have hh : M.IsHalting (M.run n (M.init w)) := Or.inl hn
    have h1 := run_stable M (M.init w) n hh (max n N) (le_max_left _ _)
    have h2 := run_stable M (M.init w) N hN (max n N) (le_max_right _ _)
    rw [← h2, h1]; exact hn
  · intro h; exact ⟨N, h⟩

theorem step_right (c : Cfg Γ M.Q) (q' : M.Q) (s' : Option Γ) (hh : ¬ M.IsHalting c)
    (hd : M.δ c.state c.head = (q', s', Move.right)) :
    M.step c = ⟨q', s' :: c.left, c.right.headD none, c.right.tail⟩ := by
  unfold TM.step; rw [if_neg hh, hd]

theorem step_left (c : Cfg Γ M.Q) (q' : M.Q) (s' : Option Γ) (hh : ¬ M.IsHalting c)
    (hd : M.δ c.state c.head = (q', s', Move.left)) :
    M.step c = ⟨q', c.left.tail, c.left.headD none, s' :: c.right⟩ := by
  obtain ⟨st, l, h, r⟩ := c
  unfold TM.step; rw [if_neg hh]; simp only at hd ⊢; rw [hd]
  cases l <;> rfl

end generic

def dec2 {Γf Γd : Type} : Option (Γf ⊕ Γd) → Option Γd
  | none => none
  | some (Sum.inl _) => none
  | some (Sum.inr g) => some g

def Tp {Γf Γd : Type} (l : List (Option (Γf ⊕ Γd))) (i : ℕ) : Option Γd :=
  (l.map dec2).getD i none

section tape

variable {Γf Γd : Type}

theorem Tp_headD {l : List (Option (Γf ⊕ Γd))} {l' : List (Option Γd)}
    (h : ∀ i, Tp l i = l'.getD i none) : dec2 (l.headD none) = l'.headD none := by
  have := h 0
  cases l <;> cases l' <;> simp_all [Tp, dec2]

theorem Tp_tail {l : List (Option (Γf ⊕ Γd))} {l' : List (Option Γd)}
    (h : ∀ i, Tp l i = l'.getD i none) : ∀ i, Tp l.tail i = l'.tail.getD i none := by
  intro i
  have := h (i + 1)
  cases l with
  | nil =>
    cases l' with
    | nil => simp [Tp]
    | cons b l' =>
      simp only [Tp, List.map_nil, List.getD_nil, List.tail_nil, List.tail_cons,
        List.getD_cons_succ] at this ⊢
      exact this
  | cons a l =>
    cases l' with
    | nil =>
      simp only [Tp, List.map_cons, List.getD_cons_succ, List.getD_nil, List.tail_cons,
        List.tail_nil] at this ⊢
      exact this
    | cons b l' =>
      simp only [Tp, List.map_cons, List.getD_cons_succ, List.tail_cons] at this ⊢
      exact this

theorem Tp_cons {x : Option (Γf ⊕ Γd)} {l : List (Option (Γf ⊕ Γd))} {y : Option Γd}
    {l' : List (Option Γd)} (hx : dec2 x = y) (h : ∀ i, Tp l i = l'.getD i none) :
    ∀ i, Tp (x :: l) i = (y :: l').getD i none := by
  intro i
  cases i with
  | zero => simpa [Tp] using hx
  | succ i => simpa [Tp] using h i

theorem Tp_none {l : List (Option (Γf ⊕ Γd))} (h : ∀ a ∈ l, dec2 a = none) :
    ∀ i, Tp l i = none := by
  induction l with
  | nil => intro i; simp [Tp]
  | cons a l ih =>
    intro i
    cases i with
    | zero => simp [Tp, h a List.mem_cons_self]
    | succ i => simpa [Tp] using ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) i

theorem dec2_map_inr (s : Option Γd) : dec2 (s.map (Sum.inr : Γd → Γf ⊕ Γd)) = s := by
  cases s <;> rfl

end tape

section machine

variable {Sym Γd : Type} (Md : TM Γd) (ι : Sym ↪ Γd)

abbrev Sym' (Sym : Type) : Type := Option (Sym ⊕ Unit)

abbrev TapeSym (Sym Γd : Type) : Type := Sym' Sym ⊕ Γd

abbrev embIn {Sym Γd : Type} (x : Sym' Sym) : Option (TapeSym Sym Γd) :=
  some (Sum.inl x)

def cδ : Bool ⊕ (Unit ⊕ Md.Q) → Option (TapeSym Sym Γd) →
    (Bool ⊕ (Unit ⊕ Md.Q)) × Option (TapeSym Sym Γd) × Move
  | Sum.inl false, some (Sum.inl (some (Sum.inl a))) =>
      (Sum.inl false, some (Sum.inr (ι a)), Move.right)
  | Sum.inl false, some (Sum.inl none) =>
      (Sum.inl true, some (Sum.inl none), Move.right)
  | Sum.inl false, s =>
      (Sum.inr (Sum.inr Md.qreject), s, Move.right)
  | Sum.inl true, none =>
      (Sum.inr (Sum.inl ()), none, Move.left)
  | Sum.inl true, some g =>
      (Sum.inr (Sum.inr Md.qreject), some g, Move.right)
  | Sum.inr (Sum.inl ()), some (Sum.inl none) =>
      (Sum.inr (Sum.inl ()), none, Move.left)
  | Sum.inr (Sum.inl ()), some (Sum.inr g) =>
      (Sum.inr (Sum.inl ()), some (Sum.inr g), Move.left)
  | Sum.inr (Sum.inl ()), s =>
      (Sum.inr (Sum.inr Md.q₀), s, Move.right)
  | Sum.inr (Sum.inr q), s =>
      (Sum.inr (Sum.inr (Md.δ q (dec2 s)).1), (Md.δ q (dec2 s)).2.1.map Sum.inr,
        (Md.δ q (dec2 s)).2.2)

@[reducible] noncomputable def checkTM : TM (TapeSym Sym Γd) where
  Q := Bool ⊕ (Unit ⊕ Md.Q)
  q₀ := Sum.inl false
  qaccept := Sum.inr (Sum.inr Md.qaccept)
  qreject := Sum.inr (Sum.inr Md.qreject)
  accept_ne_reject := fun h => Md.accept_ne_reject (by simpa using h)
  δ := cδ Md ι

theorem δ_ph3 (q : Md.Q) (s : Option (TapeSym Sym Γd)) :
    (checkTM Md ι).δ (Sum.inr (Sum.inr q)) s =
      (Sum.inr (Sum.inr (Md.δ q (dec2 s)).1), (Md.δ q (dec2 s)).2.1.map Sum.inr,
        (Md.δ q (dec2 s)).2.2) := rfl

theorem scan_prefix : ∀ (w : List Sym) (rest : List (Sym' Sym)) (A : List (Option (TapeSym Sym Γd))),
    (checkTM Md ι).run w.length
      ⟨Sum.inl false, A,
        ((w.map (some ∘ Sum.inl) ++ rest).map embIn).headD none,
        ((w.map (some ∘ Sum.inl) ++ rest).map embIn).tail⟩ =
      ⟨Sum.inl false,
        (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse ++ A,
        (rest.map embIn).headD none,
        (rest.map embIn).tail⟩ := by
  intro w
  induction w with
  | nil =>
    intro rest A
    simp [TM.run]
  | cons a w ih =>
    intro rest A
    have hnh : ¬ (checkTM Md ι).IsHalting
        ⟨Sum.inl false, A,
          some (Sum.inl (some (Sum.inl a))),
          ((w.map (some ∘ Sum.inl) ++ rest).map embIn)⟩ := by
      simp [TM.IsHalting]
    have hd : (checkTM Md ι).δ (Sum.inl false) (some (Sum.inl (some (Sum.inl a)))) =
        (Sum.inl false, some (Sum.inr (ι a)), Move.right) := rfl
    simp only [List.map_cons, List.cons_append, Function.comp_apply, List.headD_cons,
      List.tail_cons, List.length_cons]
    rw [run_succ, step_right _ _ _ _ hnh hd]
    rw [ih rest (some (Sum.inr (ι a)) :: A)]
    simp [List.reverse_cons, List.append_assoc]

theorem rewind : ∀ (u : List Sym) (b : Sym) (R : List (Option (TapeSym Sym Γd))),
    (checkTM Md ι).run (u.length + 1)
      ⟨Sum.inr (Sum.inl ()), u.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))),
        some (Sum.inr (ι b)), R⟩ =
      ⟨Sum.inr (Sum.inl ()), [], none,
        (b :: u).reverse.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))) ++ R⟩ := by
  intro u
  induction u with
  | nil =>
    intro b R
    have hnh : ¬ (checkTM Md ι).IsHalting
        ⟨Sum.inr (Sum.inl ()), [], some (Sum.inr (ι b)), R⟩ := by simp [TM.IsHalting]
    have hd : (checkTM Md ι).δ (Sum.inr (Sum.inl ())) (some (Sum.inr (ι b))) =
        (Sum.inr (Sum.inl ()), some (Sum.inr (ι b)), Move.left) := rfl
    rw [List.length_nil, List.map_nil, run_succ, step_left _ _ _ _ hnh hd]
    rfl
  | cons c u ih =>
    intro b R
    have hnh : ¬ (checkTM Md ι).IsHalting
        ⟨Sum.inr (Sum.inl ()),
          (c :: u).map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))),
          some (Sum.inr (ι b)), R⟩ := by simp [TM.IsHalting]
    have hd : (checkTM Md ι).δ (Sum.inr (Sum.inl ())) (some (Sum.inr (ι b))) =
        (Sum.inr (Sum.inl ()), some (Sum.inr (ι b)), Move.left) := rfl
    rw [List.length_cons, run_succ, step_left _ _ _ _ hnh hd]
    simp only [List.map_cons, List.tail_cons, List.headD_cons]
    rw [ih c (some (Sum.inr (ι b)) :: R)]
    simp

theorem phase12_valid (w : List Sym) :
    (checkTM Md ι).run (2 * w.length + 4)
      ((checkTM Md ι).init ((w.map (some ∘ Sum.inl) ++ [none]).map Function.Embedding.inl)) =
      ⟨Sum.inr (Sum.inr Md.q₀), [none],
        (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))) ++
          [none, none]).headD none,
        (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))) ++
          [none, none]).tail⟩ := by
  have hinit : (checkTM Md ι).init ((w.map (some ∘ Sum.inl) ++ [none]).map Function.Embedding.inl) =
      ⟨Sum.inl false, [],
        ((w.map (some ∘ Sum.inl) ++ [none]).map embIn).headD none,
        ((w.map (some ∘ Sum.inl) ++ [none]).map embIn).tail⟩ := by
    simp [TM.init, List.map_map, Function.comp_def, embIn]
  have h1 := scan_prefix Md ι w [none] []
  simp only [List.append_nil, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons] at h1
  have hnh1 : ¬ (checkTM Md ι).IsHalting
      ⟨Sum.inl false,
        (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
        some (Sum.inl none), []⟩ := by simp [TM.IsHalting]
  have hd1 : (checkTM Md ι).δ (Sum.inl false) (some (Sum.inl none)) =
      (Sum.inl true, some (Sum.inl none), Move.right) := rfl
  have hnh2 : ¬ (checkTM Md ι).IsHalting
      ⟨Sum.inl true,
        some (Sum.inl none) ::
          (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
        none, []⟩ := by simp [TM.IsHalting]
  have hd2 : (checkTM Md ι).δ (Sum.inl true) none =
      (Sum.inr (Sum.inl ()), none, Move.left) := rfl
  have hnh3 : ¬ (checkTM Md ι).IsHalting
      ⟨Sum.inr (Sum.inl ()),
        (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
        some (Sum.inl none), [none]⟩ := by simp [TM.IsHalting]
  have hd3 : (checkTM Md ι).δ (Sum.inr (Sum.inl ())) (some (Sum.inl none)) =
      (Sum.inr (Sum.inl ()), none, Move.left) := rfl
  have h3 : (checkTM Md ι).run (w.length + 3)
      ((checkTM Md ι).init ((w.map (some ∘ Sum.inl) ++ [none]).map Function.Embedding.inl)) =
      ⟨Sum.inr (Sum.inl ()),
        ((w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse).tail,
        ((w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse).headD none,
        [none, none]⟩ := by
    rw [hinit, show w.length + 3 = w.length + 1 + 1 + 1 from rfl,
      run_succ', run_succ', run_succ', h1]
    rw [step_right _ _ _ _ hnh1 hd1]
    simp only [List.headD_nil, List.tail_nil]
    rw [step_left _ _ _ _ hnh2 hd2]
    simp only [List.tail_cons, List.headD_cons]
    rw [step_left _ _ _ _ hnh3 hd3]
  have h4 : (checkTM Md ι).run w.length
      ⟨Sum.inr (Sum.inl ()),
        ((w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse).tail,
        ((w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse).headD none,
        [none, none]⟩ =
      ⟨Sum.inr (Sum.inl ()), [], none,
        w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))) ++ [none, none]⟩ := by
    rcases hw : w.reverse with _ | ⟨b, u⟩
    · have : w = [] := List.reverse_eq_nil_iff.1 hw
      subst this
      rfl
    · have hw' : w = u.reverse ++ [b] := by
        rw [← List.reverse_reverse w, hw]; simp
      have hl : w.length = u.length + 1 := by rw [hw']; simp
      have hmr : (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse =
          some (Sum.inr (ι b)) ::
            u.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))) := by
        rw [hw']; simp
      rw [hmr, hl]
      simp only [List.tail_cons, List.headD_cons]
      rw [rewind Md ι u b [none, none], hw']
      simp
  have hnh4 : ¬ (checkTM Md ι).IsHalting
      ⟨Sum.inr (Sum.inl ()), [], none,
        w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))) ++ [none, none]⟩ := by
    simp [TM.IsHalting]
  have hd4 : (checkTM Md ι).δ (Sum.inr (Sum.inl ())) none =
      (Sum.inr (Sum.inr Md.q₀), none, Move.right) := rfl
  rw [show 2 * w.length + 4 = (w.length + 3) + w.length + 1 by omega,
    run_succ', run_add _ (w.length + 3) w.length, h3, h4]
  rw [step_right _ _ _ _ hnh4 hd4]

def Rel (c : Cfg (TapeSym Sym Γd) (checkTM Md ι).Q) (d : Cfg Γd Md.Q) : Prop :=
  c.state = Sum.inr (Sum.inr d.state) ∧ dec2 c.head = d.head ∧
    (∀ i, Tp c.left i = d.left.getD i none) ∧ (∀ i, Tp c.right i = d.right.getD i none)

theorem step_rel (c : Cfg (TapeSym Sym Γd) (checkTM Md ι).Q) (d : Cfg Γd Md.Q)
    (h : Rel Md ι c d) :
    Rel Md ι ((checkTM Md ι).step c) (Md.step d) := by
  obtain ⟨hs, hh, hl, hr⟩ := h
  by_cases hd : Md.IsHalting d
  · have hc : (checkTM Md ι).IsHalting c := by
      rcases hd with h1 | h1
      · left; rw [hs, h1]
      · right; rw [hs, h1]
    rw [step_halt _ c hc, step_halt _ d hd]; exact ⟨hs, hh, hl, hr⟩
  · have hc : ¬ (checkTM Md ι).IsHalting c := by
      rintro (h1 | h1) <;> apply hd
      · left; rw [hs] at h1; simpa using h1
      · right; rw [hs] at h1; simpa using h1
    rcases hδ : Md.δ d.state d.head with ⟨q', s', mv⟩
    have hδc : (checkTM Md ι).δ c.state c.head = (Sum.inr (Sum.inr q'), s'.map Sum.inr, mv) := by
      rw [hs, δ_ph3, hh, hδ]
    cases mv
    · rw [step_left _ c _ _ hc hδc, step_left Md d _ _ hd hδ]
      exact ⟨rfl, Tp_headD hl, Tp_tail hl, Tp_cons (dec2_map_inr s') hr⟩
    · rw [step_right _ c _ _ hc hδc, step_right Md d _ _ hd hδ]
      exact ⟨rfl, Tp_headD hr, Tp_cons (dec2_map_inr s') hl, Tp_tail hr⟩

theorem run_rel (c : Cfg (TapeSym Sym Γd) (checkTM Md ι).Q) (d : Cfg Γd Md.Q)
    (h : Rel Md ι c d) :
    ∀ n, Rel Md ι ((checkTM Md ι).run n c) (Md.run n d) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => rw [run_succ', run_succ']; exact step_rel Md ι _ _ ih

theorem rel_halting (c : Cfg (TapeSym Sym Γd) (checkTM Md ι).Q) (d : Cfg Γd Md.Q)
    (h : Rel Md ι c d) : (checkTM Md ι).IsHalting c ↔ Md.IsHalting d := by
  unfold TM.IsHalting
  rw [h.1]
  simp

theorem rel_accept (c : Cfg (TapeSym Sym Γd) (checkTM Md ι).Q) (d : Cfg Γd Md.Q)
    (h : Rel Md ι c d) : c.state = (checkTM Md ι).qaccept ↔ d.state = Md.qaccept := by
  rw [h.1]
  simp

theorem init_rel (w : List Sym) :
    Rel Md ι
      ⟨Sum.inr (Sum.inr Md.q₀), [none],
        (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))) ++
          [none, none]).headD none,
        (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))) ++
          [none, none]).tail⟩
      (Md.init (w.map ι)) := by
  have hY : ∀ i, Tp (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd))) ++
      [none, none]) i = ((w.map ι).map some).getD i none := by
    induction w with
    | nil =>
      intro i
      simp only [List.map_nil, List.nil_append, List.getD_nil]
      exact Tp_none (fun a ha => by simp at ha; subst ha; rfl) i
    | cons a w ih =>
      intro i
      cases i with
      | zero => simp [Tp, dec2]
      | succ i => simpa [Tp] using ih i
  have hL : ∀ i, Tp ([none] : List (Option (TapeSym Sym Γd))) i =
      ([] : List (Option Γd)).getD i none := by
    intro i
    rw [List.getD_nil]
    exact Tp_none (fun a ha => by simp at ha; subst ha; rfl) i
  exact ⟨rfl, Tp_headD hY, hL, Tp_tail hY⟩

theorem decomp_input (s : List (Sym' Sym)) :
    (∃ w : List Sym, s = w.map (some ∘ Sum.inl)) ∨
    (∃ (w : List Sym) (rest : List (Sym' Sym)),
      s = w.map (some ∘ Sum.inl) ++ some (Sum.inr ()) :: rest) ∨
    (∃ w : List Sym, s = w.map (some ∘ Sum.inl) ++ [none]) ∨
    (∃ (w : List Sym) (d : Sym' Sym) (rest : List (Sym' Sym)),
      s = w.map (some ∘ Sum.inl) ++ none :: d :: rest) := by
  induction s with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons x s ih =>
    rcases x with _ | (a | u)
    · cases s with
      | nil => exact Or.inr (Or.inr (Or.inl ⟨[], rfl⟩))
      | cons d rest => exact Or.inr (Or.inr (Or.inr ⟨[], d, rest, rfl⟩))
    · rcases ih with ⟨w, rfl⟩ | ⟨w, rest, rfl⟩ | ⟨w, rfl⟩ | ⟨w, d, rest, rfl⟩
      · exact Or.inl ⟨a :: w, rfl⟩
      · exact Or.inr (Or.inl ⟨a :: w, rest, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨a :: w, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨a :: w, d, rest, rfl⟩))
    · cases u
      exact Or.inr (Or.inl ⟨[], s, rfl⟩)

theorem map_inl_inj {w₁ w₂ : List Sym}
    (h : w₁.map (some ∘ Sum.inl : Sym → Sym' Sym) = w₂.map (some ∘ Sum.inl)) : w₁ = w₂ := by
  apply List.map_injective_iff.2 _ h
  intro a b hab
  exact Sum.inl.inj (Option.some.inj hab)

theorem not_none_mem_map_inl (w : List Sym) :
    (none : Sym' Sym) ∉ w.map (some ∘ Sum.inl) := by
  intro h
  rw [List.mem_map] at h
  obtain ⟨a, -, ha⟩ := h
  nomatch ha

theorem not_inr_mem_map_inl (w : List Sym) :
    (some (Sum.inr ()) : Sym' Sym) ∉ w.map (some ∘ Sum.inl) := by
  intro h
  rw [List.mem_map] at h
  obtain ⟨a, -, ha⟩ := h
  nomatch ha

theorem map_inl_append_none_inj {w₁ w₂ : List Sym} {r₁ r₂ : List (Sym' Sym)}
    (h : w₁.map (some ∘ Sum.inl : Sym → Sym' Sym) ++ none :: r₁ =
      w₂.map (some ∘ Sum.inl) ++ none :: r₂) : w₁ = w₂ ∧ r₁ = r₂ := by
  induction w₁ generalizing w₂ with
  | nil =>
    cases w₂ with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, h⟩
    | cons b w₂ =>
      simp only [List.map_nil, List.nil_append, List.map_cons, Function.comp_apply,
        List.cons_append, List.cons.injEq] at h
      nomatch h.1
  | cons a w₁ ih =>
    cases w₂ with
    | nil =>
      simp only [List.map_cons, Function.comp_apply, List.cons_append, List.map_nil,
        List.nil_append, List.cons.injEq] at h
      nomatch h.1
    | cons b w₂ =>
      simp only [List.map_cons, Function.comp_apply, List.cons_append, List.cons.injEq] at h
      have hab : a = b := Sum.inl.inj (Option.some.inj h.1)
      subst hab
      obtain ⟨rfl, rfl⟩ := ih h.2
      exact ⟨rfl, rfl⟩

end machine

theorem poly_gen (c d : ℕ) : ∃ K, ∀ n : ℕ, c * (n + 1) ^ d ≤ n ^ K + K := by
  refine ⟨c * (c * 2 ^ d + 1) ^ d + d + 1, fun n => ?_⟩
  by_cases hn : n ≤ c * 2 ^ d
  · have h1 : c * (n + 1) ^ d ≤ c * (c * 2 ^ d + 1) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  · push Not at hn
    have hn1 : 1 ≤ n := by omega
    have h2 : (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) _
    have h3 : c * (n + 1) ^ d ≤ c * 2 ^ d * n ^ d := by
      calc c * (n + 1) ^ d ≤ c * (2 * n) ^ d := Nat.mul_le_mul_left _ h2
        _ = c * 2 ^ d * n ^ d := by rw [mul_pow, mul_assoc]
    have h4 : c * 2 ^ d * n ^ d ≤ n * n ^ d := Nat.mul_le_mul_right _ hn.le
    have h5 : n * n ^ d = n ^ (d + 1) := by ring
    have h6 : n ^ (d + 1) ≤ n ^ (c * (c * 2 ^ d + 1) ^ d + d + 1) :=
      Nat.pow_le_pow_right hn1 (by omega)
    omega

theorem time_bound (kd : ℕ) : ∃ K, ∀ n : ℕ, 2 * n + 4 + (n ^ kd + kd) ≤ n ^ K + K := by
  obtain ⟨K, hK⟩ := poly_gen (kd + 7) (kd + 1)
  refine ⟨K, fun n => ?_⟩
  have hu1 : 1 ≤ n + 1 := by omega
  have e1 : n ^ kd ≤ (n + 1) ^ kd := Nat.pow_le_pow_left (by omega) _
  have e2 : (n + 1) ^ kd ≤ (n + 1) ^ (kd + 1) := Nat.pow_le_pow_right hu1 (by omega)
  have e3 : n + 1 ≤ (n + 1) ^ (kd + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hu1 (by omega)
  have e4 : 1 ≤ (n + 1) ^ (kd + 1) := Nat.one_le_pow _ _ (by omega)
  have e5 : kd ≤ kd * (n + 1) ^ (kd + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hle : 2 * n + 4 + (n ^ kd + kd) ≤ (kd + 7) * (n + 1) ^ (kd + 1) := by nlinarith
  exact le_trans hle (hK n)

end CookPSubsetNP

open CookPvsNP CookPSubsetNP in
theorem solution (Sym : Type) [Fintype Sym] : P Sym ⊆ NP Sym := by
  intro L hL
  obtain ⟨Γd, hΓd, ι, Md, kd, hhalt, hacc⟩ := hL
  let R : List Sym → List Unit → Prop := fun w y => w ∈ L ∧ y = []
  refine ⟨Unit, inferInstance, ⟨()⟩, R, 0, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := time_bound kd
    have hfin : Fintype (TapeSym Sym Γd) := by haveI := hΓd; infer_instance
    have hkey : ∀ s : List (Sym' Sym),
        ∃ N, N ≤ 2 * s.length + 4 + (s.length ^ kd + kd) ∧
          (checkTM Md ι).HaltsWithin N (s.map Function.Embedding.inl) ∧
          ((checkTM Md ι).Accepts (s.map Function.Embedding.inl) ↔ s ∈ checkLang R) := by
      intro s
      have hinit_eq : (checkTM Md ι).init (s.map Function.Embedding.inl) =
          ⟨Sum.inl false, [], (s.map embIn).headD none, (s.map embIn).tail⟩ := by
        simp [TM.init, List.map_map, Function.comp_def]
      rcases decomp_input s with ⟨w, rfl⟩ | ⟨w, rest, rfl⟩ | ⟨w, rfl⟩ | ⟨w, d, rest, rfl⟩
      · refine ⟨w.length + 1, ?_, ?_, ?_⟩
        · simp [List.length_map]; omega
        · have h1 := scan_prefix Md ι w [] []
          simp only [List.append_nil, List.map_nil, List.headD_nil, List.tail_nil] at h1
          have hnh : ¬ (checkTM Md ι).IsHalting
              ⟨Sum.inl false,
                (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                none, []⟩ := by simp [TM.IsHalting]
          have hd : (checkTM Md ι).δ (Sum.inl false) none =
              (Sum.inr (Sum.inr Md.qreject), none, Move.right) := rfl
          have hrun : (checkTM Md ι).run (w.length + 1)
              ((checkTM Md ι).init ((w.map (some ∘ Sum.inl)).map Function.Embedding.inl)) =
              ⟨Sum.inr (Sum.inr Md.qreject),
                none :: (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                none, []⟩ := by
            rw [hinit_eq, run_succ', h1, step_right _ _ _ _ hnh hd]
            rfl
          unfold TM.HaltsWithin; rw [hrun]; right; rfl
        · have h1 := scan_prefix Md ι w [] []
          simp only [List.append_nil, List.map_nil, List.headD_nil, List.tail_nil] at h1
          have hnh : ¬ (checkTM Md ι).IsHalting
              ⟨Sum.inl false,
                (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                none, []⟩ := by simp [TM.IsHalting]
          have hd : (checkTM Md ι).δ (Sum.inl false) none =
              (Sum.inr (Sum.inr Md.qreject), none, Move.right) := rfl
          have hrun : (checkTM Md ι).run (w.length + 1)
              ((checkTM Md ι).init ((w.map (some ∘ Sum.inl)).map Function.Embedding.inl)) =
              ⟨Sum.inr (Sum.inr Md.qreject),
                none :: (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                none, []⟩ := by
            rw [hinit_eq, run_succ', h1, step_right _ _ _ _ hnh hd]
            rfl
          have hH : (checkTM Md ι).HaltsWithin (w.length + 1)
              ((w.map (some ∘ Sum.inl)).map Function.Embedding.inl) := by
            unfold TM.HaltsWithin; rw [hrun]; right; rfl
          rw [accepts_iff _ _ _ hH, hrun]
          constructor
          · intro h; exact absurd (by simpa using h) Md.accept_ne_reject.symm
          · rintro ⟨w', y', ⟨_, rfl⟩, heq⟩
            have hmem : (none : Sym' Sym) ∈ w.map (some ∘ Sum.inl) := by
              rw [heq]; simp
            exact absurd hmem (not_none_mem_map_inl w)
      · refine ⟨w.length + 1, ?_, ?_, ?_⟩
        · simp [List.length_append, List.length_map]; omega
        · have h1 := scan_prefix Md ι w (some (Sum.inr ()) :: rest) []
          simp only [List.append_nil, List.map_cons, List.headD_cons, List.tail_cons] at h1
          have hnh : ¬ (checkTM Md ι).IsHalting
              ⟨Sum.inl false,
                (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                embIn (some (Sum.inr ())), rest.map embIn⟩ := by simp [TM.IsHalting]
          have hd : (checkTM Md ι).δ (Sum.inl false) (embIn (some (Sum.inr ()))) =
              (Sum.inr (Sum.inr Md.qreject), embIn (some (Sum.inr ())), Move.right) := rfl
          have hrun : (checkTM Md ι).run (w.length + 1)
              ((checkTM Md ι).init
                ((w.map (some ∘ Sum.inl) ++ some (Sum.inr ()) :: rest).map Function.Embedding.inl)) =
              ⟨Sum.inr (Sum.inr Md.qreject),
                embIn (some (Sum.inr ())) ::
                  (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                (rest.map embIn).headD none, (rest.map embIn).tail⟩ := by
            rw [hinit_eq, run_succ', h1, step_right _ _ _ _ hnh hd]
          unfold TM.HaltsWithin; rw [hrun]; right; rfl
        · have h1 := scan_prefix Md ι w (some (Sum.inr ()) :: rest) []
          simp only [List.append_nil, List.map_cons, List.headD_cons, List.tail_cons] at h1
          have hnh : ¬ (checkTM Md ι).IsHalting
              ⟨Sum.inl false,
                (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                embIn (some (Sum.inr ())), rest.map embIn⟩ := by simp [TM.IsHalting]
          have hd : (checkTM Md ι).δ (Sum.inl false) (embIn (some (Sum.inr ()))) =
              (Sum.inr (Sum.inr Md.qreject), embIn (some (Sum.inr ())), Move.right) := rfl
          have hrun : (checkTM Md ι).run (w.length + 1)
              ((checkTM Md ι).init
                ((w.map (some ∘ Sum.inl) ++ some (Sum.inr ()) :: rest).map Function.Embedding.inl)) =
              ⟨Sum.inr (Sum.inr Md.qreject),
                embIn (some (Sum.inr ())) ::
                  (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                (rest.map embIn).headD none, (rest.map embIn).tail⟩ := by
            rw [hinit_eq, run_succ', h1, step_right _ _ _ _ hnh hd]
          have hH : (checkTM Md ι).HaltsWithin (w.length + 1)
              ((w.map (some ∘ Sum.inl) ++ some (Sum.inr ()) :: rest).map Function.Embedding.inl) := by
            unfold TM.HaltsWithin; rw [hrun]; right; rfl
          rw [accepts_iff _ _ _ hH, hrun]
          constructor
          · intro h; exact absurd (by simpa using h) Md.accept_ne_reject.symm
          · rintro ⟨w', y', ⟨_, rfl⟩, heq⟩
            simp only [List.map_nil] at heq
            have hmem : (some (Sum.inr ()) : Sym' Sym) ∈ w'.map (some ∘ Sum.inl) ++ [none] := by
              rw [← heq]; simp
            simp only [List.mem_append, List.mem_singleton] at hmem
            rcases hmem with hmem | hmem
            · exact absurd hmem (not_inr_mem_map_inl w')
            · nomatch hmem
      · refine ⟨2 * w.length + 4 + (w.length ^ kd + kd), ?_, ?_, ?_⟩
        · have hlen : (w.map (some ∘ Sum.inl : Sym → Sym' Sym) ++ [none]).length = w.length + 1 := by
            simp
          have hpow : w.length ^ kd ≤ (w.length + 1) ^ kd := Nat.pow_le_pow_left (by omega) kd
          rw [hlen]; omega
        · have h12 := phase12_valid Md ι w
          have hrel := run_rel Md ι _ _ (init_rel Md ι w) (w.length ^ kd + kd)
          unfold TM.HaltsWithin
          rw [run_add, h12]
          exact (rel_halting Md ι _ _ hrel).2 (hhalt w)
        · have h12 := phase12_valid Md ι w
          have hrel := run_rel Md ι _ _ (init_rel Md ι w) (w.length ^ kd + kd)
          have hH : (checkTM Md ι).HaltsWithin (2 * w.length + 4 + (w.length ^ kd + kd))
              ((w.map (some ∘ Sum.inl) ++ [none]).map Function.Embedding.inl) := by
            unfold TM.HaltsWithin
            rw [run_add, h12]
            exact (rel_halting Md ι _ _ hrel).2 (hhalt w)
          rw [accepts_iff _ _ _ hH, run_add, h12, rel_accept Md ι _ _ hrel,
            ← accepts_iff Md _ _ (hhalt w), ← hacc w]
          constructor
          · intro hw
            exact ⟨w, [], ⟨hw, rfl⟩, rfl⟩
          · rintro ⟨w', y', ⟨hw', rfl⟩, heq⟩
            obtain ⟨rfl, -⟩ := map_inl_append_none_inj heq
            exact hw'
      · refine ⟨w.length + 2, ?_, ?_, ?_⟩
        · simp [List.length_append, List.length_map]; omega
        · have h1 := scan_prefix Md ι w (none :: d :: rest) []
          simp only [List.append_nil, List.map_cons, List.headD_cons, List.tail_cons] at h1
          have hnh1 : ¬ (checkTM Md ι).IsHalting
              ⟨Sum.inl false,
                (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                embIn none, embIn d :: rest.map embIn⟩ := by simp [TM.IsHalting]
          have hd1 : (checkTM Md ι).δ (Sum.inl false) (embIn none) =
              (Sum.inl true, embIn none, Move.right) := rfl
          have hnh2 : ¬ (checkTM Md ι).IsHalting
              ⟨Sum.inl true,
                embIn none ::
                  (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                embIn d, rest.map embIn⟩ := by simp [TM.IsHalting]
          have hd2 : (checkTM Md ι).δ (Sum.inl true) (embIn d) =
              (Sum.inr (Sum.inr Md.qreject), embIn d, Move.right) := rfl
          have hrun : (checkTM Md ι).run (w.length + 2)
              ((checkTM Md ι).init
                ((w.map (some ∘ Sum.inl) ++ none :: d :: rest).map Function.Embedding.inl)) =
              ⟨Sum.inr (Sum.inr Md.qreject),
                embIn d :: embIn none ::
                  (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                (rest.map embIn).headD none, (rest.map embIn).tail⟩ := by
            rw [hinit_eq, show w.length + 2 = w.length + 1 + 1 from rfl,
              run_succ', run_succ', h1, step_right _ _ _ _ hnh1 hd1]
            simp only [List.headD_cons, List.tail_cons]
            rw [step_right _ _ _ _ hnh2 hd2]
          unfold TM.HaltsWithin; rw [hrun]; right; rfl
        · have h1 := scan_prefix Md ι w (none :: d :: rest) []
          simp only [List.append_nil, List.map_cons, List.headD_cons, List.tail_cons] at h1
          have hnh1 : ¬ (checkTM Md ι).IsHalting
              ⟨Sum.inl false,
                (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                embIn none, embIn d :: rest.map embIn⟩ := by simp [TM.IsHalting]
          have hd1 : (checkTM Md ι).δ (Sum.inl false) (embIn none) =
              (Sum.inl true, embIn none, Move.right) := rfl
          have hnh2 : ¬ (checkTM Md ι).IsHalting
              ⟨Sum.inl true,
                embIn none ::
                  (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                embIn d, rest.map embIn⟩ := by simp [TM.IsHalting]
          have hd2 : (checkTM Md ι).δ (Sum.inl true) (embIn d) =
              (Sum.inr (Sum.inr Md.qreject), embIn d, Move.right) := rfl
          have hrun : (checkTM Md ι).run (w.length + 2)
              ((checkTM Md ι).init
                ((w.map (some ∘ Sum.inl) ++ none :: d :: rest).map Function.Embedding.inl)) =
              ⟨Sum.inr (Sum.inr Md.qreject),
                embIn d :: embIn none ::
                  (w.map (fun a => (some (Sum.inr (ι a)) : Option (TapeSym Sym Γd)))).reverse,
                (rest.map embIn).headD none, (rest.map embIn).tail⟩ := by
            rw [hinit_eq, show w.length + 2 = w.length + 1 + 1 from rfl,
              run_succ', run_succ', h1, step_right _ _ _ _ hnh1 hd1]
            simp only [List.headD_cons, List.tail_cons]
            rw [step_right _ _ _ _ hnh2 hd2]
          have hH : (checkTM Md ι).HaltsWithin (w.length + 2)
              ((w.map (some ∘ Sum.inl) ++ none :: d :: rest).map Function.Embedding.inl) := by
            unfold TM.HaltsWithin; rw [hrun]; right; rfl
          rw [accepts_iff _ _ _ hH, hrun]
          constructor
          · intro h; exact absurd (by simpa using h) Md.accept_ne_reject.symm
          · rintro ⟨w', y', ⟨_, rfl⟩, heq⟩
            obtain ⟨_, hnil⟩ := map_inl_append_none_inj heq
            nomatch hnil
    refine ⟨TapeSym Sym Γd, hfin, Function.Embedding.inl, checkTM Md ι, K, ?_, ?_⟩
    · intro s
      obtain ⟨N, hN, hH, -⟩ := hkey s
      have hle : N ≤ s.length ^ K + K := le_trans hN (hK s.length)
      unfold TM.HaltsWithin at hH ⊢
      rw [run_stable _ _ N hH _ hle]
      exact hH
    · intro s
      obtain ⟨N, -, -, hA⟩ := hkey s
      exact hA.symm
  · intro w
    constructor
    · intro hw
      exact ⟨[], by simp, hw, rfl⟩
    · rintro ⟨y, -, hw, -⟩
      exact hw
