-- Prove2me | solution 1 for CookPvsNP.mem_P_of_polyReducible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T10:44:44.727122+00:00
-- url     : https://prove2.me/submissions/1b0cdb83-0807-49fd-bb16-95b1bd7f2b54

import Mathlib
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace CookRed

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

theorem step_right_length (c : Cfg Γ M.Q) : (M.step c).right.length ≤ c.right.length + 1 := by
  by_cases hh : M.IsHalting c
  · rw [step_halt M c hh]; omega
  · rcases hd : M.δ c.state c.head with ⟨q', s', mv⟩
    cases mv
    · rw [step_left M c q' s' hh hd]; simp
    · rw [step_right M c q' s' hh hd]; simp; omega

theorem run_right_length (c : Cfg Γ M.Q) (n : ℕ) :
    (M.run n c).right.length ≤ c.right.length + n := by
  induction n with
  | zero => simp [TM.run]
  | succ n ih => rw [run_succ']; have := step_right_length M (M.run n c); omega

theorem out_decomp (c : Cfg Γ M.Q) :
    ∃ m, c.head :: c.right = M.output c ++ List.replicate m none := by
  unfold TM.output
  generalize c.head :: c.right = l
  have h1 := List.takeWhile_append_dropWhile (p := Option.isNone) (l := l.reverse)
  have h2 : l.reverse.takeWhile Option.isNone =
      List.replicate (l.reverse.takeWhile Option.isNone).length none := by
    rw [List.eq_replicate_iff]; refine ⟨rfl, fun b hb => ?_⟩
    have := List.mem_takeWhile_imp hb
    simpa using this
  refine ⟨(l.reverse.takeWhile Option.isNone).length, ?_⟩
  have h3 : l = (l.reverse.dropWhile Option.isNone).reverse ++
      (l.reverse.takeWhile Option.isNone).reverse := by
    rw [← List.reverse_append, h1, List.reverse_reverse]
  rw [h2, List.reverse_replicate] at h3
  exact h3

end generic

def dec1 {Γf Γd : Type} : Option (Γf ⊕ Γd) → Option Γf
  | none => none
  | some (Sum.inl g) => some g
  | some (Sum.inr _) => none

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

theorem dec1_map_inl (s : Option Γf) : dec1 (s.map (Sum.inl : Γf → Γf ⊕ Γd)) = s := by
  cases s <;> rfl

theorem getD_map_inl (o : Option (Option Γf)) :
    (o.map (Option.map (Sum.inl : Γf → Γf ⊕ Γd))).getD none = (o.getD none).map Sum.inl := by
  cases o <;> rfl

theorem headD_map_inl (l : List (Option Γf)) :
    (l.map (Option.map (Sum.inl : Γf → Γf ⊕ Γd))).headD none = (l.headD none).map Sum.inl := by
  cases l <;> rfl

end tape

section machine

variable {Γf Γd Sym₂ : Type} (Mf : TM Γf) (Md : TM Γd) (ι₂ : Sym₂ ↪ Γf) (ι : Sym₂ ↪ Γd)

open Classical in
noncomputable def sweepδ (q : Mf.Q) :
    Option (Γf ⊕ Γd) → (Mf.Q ⊕ (Unit ⊕ Md.Q)) × Option (Γf ⊕ Γd) × Move
  | none => (Sum.inr (Sum.inl ()), none, Move.left)
  | some (Sum.inl g) =>
      if h : ∃ a, ι₂ a = g then (Sum.inl q, some (Sum.inr (ι h.choose)), Move.right)
      else (Sum.inr (Sum.inl ()), some (Sum.inl g), Move.left)
  | some (Sum.inr g) => (Sum.inr (Sum.inl ()), some (Sum.inr g), Move.left)

noncomputable def cδ :
    Mf.Q ⊕ (Unit ⊕ Md.Q) → Option (Γf ⊕ Γd) → (Mf.Q ⊕ (Unit ⊕ Md.Q)) × Option (Γf ⊕ Γd) × Move
  | Sum.inl q, s =>
      if q = Mf.qaccept ∨ q = Mf.qreject then sweepδ Mf Md ι₂ ι q s else
        (Sum.inl (Mf.δ q (dec1 s)).1, (Mf.δ q (dec1 s)).2.1.map Sum.inl, (Mf.δ q (dec1 s)).2.2)
  | Sum.inr (Sum.inl _), none => (Sum.inr (Sum.inr Md.q₀), none, Move.right)
  | Sum.inr (Sum.inl _), some (Sum.inl g) => (Sum.inr (Sum.inr Md.q₀), some (Sum.inl g), Move.right)
  | Sum.inr (Sum.inl _), some (Sum.inr g) => (Sum.inr (Sum.inl ()), some (Sum.inr g), Move.left)
  | Sum.inr (Sum.inr q), s =>
      (Sum.inr (Sum.inr (Md.δ q (dec2 s)).1), (Md.δ q (dec2 s)).2.1.map Sum.inr,
        (Md.δ q (dec2 s)).2.2)

@[reducible] noncomputable def compTM : TM (Γf ⊕ Γd) where
  Q := Mf.Q ⊕ (Unit ⊕ Md.Q)
  q₀ := Sum.inl Mf.q₀
  qaccept := Sum.inr (Sum.inr Md.qaccept)
  qreject := Sum.inr (Sum.inr Md.qreject)
  accept_ne_reject := fun h => Md.accept_ne_reject (by simpa using h)
  δ := cδ Mf Md ι₂ ι

theorem δ_sweep_H (q : Mf.Q) (hq : q = Mf.qaccept ∨ q = Mf.qreject) (a : Sym₂) :
    (compTM Mf Md ι₂ ι).δ (Sum.inl q) (some (Sum.inl (ι₂ a))) =
      (Sum.inl q, some (Sum.inr (ι a)), Move.right) := by
  have hex : ∃ a', ι₂ a' = ι₂ a := ⟨a, rfl⟩
  have hch : hex.choose = a := ι₂.injective hex.choose_spec
  show cδ Mf Md ι₂ ι (Sum.inl q) (some (Sum.inl (ι₂ a))) = _
  simp only [cδ, if_pos hq, sweepδ]
  rw [dif_pos hex, hch]

theorem δ_sweep_none (q : Mf.Q) (hq : q = Mf.qaccept ∨ q = Mf.qreject) :
    (compTM Mf Md ι₂ ι).δ (Sum.inl q) none = (Sum.inr (Sum.inl ()), none, Move.left) := by
  show cδ Mf Md ι₂ ι (Sum.inl q) none = _
  simp only [cδ, if_pos hq, sweepδ]

theorem δ_rw_G (g : Γd) :
    (compTM Mf Md ι₂ ι).δ (Sum.inr (Sum.inl ())) (some (Sum.inr g)) =
      (Sum.inr (Sum.inl ()), some (Sum.inr g), Move.left) := rfl

theorem δ_rw_other (s : Option (Γf ⊕ Γd)) (hs : dec2 s = none) :
    (compTM Mf Md ι₂ ι).δ (Sum.inr (Sum.inl ())) s = (Sum.inr (Sum.inr Md.q₀), s, Move.right) := by
  rcases s with _ | (g | g)
  · rfl
  · rfl
  · simp [dec2] at hs

theorem δ_ph3 (q : Md.Q) (s : Option (Γf ⊕ Γd)) :
    (compTM Mf Md ι₂ ι).δ (Sum.inr (Sum.inr q)) s =
      (Sum.inr (Sum.inr (Md.δ q (dec2 s)).1), (Md.δ q (dec2 s)).2.1.map Sum.inr,
        (Md.δ q (dec2 s)).2.2) := by
  rcases s with _ | (g | g) <;> rfl

/-! Phase 1: simulation of the reducer. -/

def emb1 (c : Cfg Γf Mf.Q) : Cfg (Γf ⊕ Γd) (compTM Mf Md ι₂ ι).Q :=
  ⟨Sum.inl c.state, c.left.map (Option.map Sum.inl), c.head.map Sum.inl,
    c.right.map (Option.map Sum.inl)⟩

theorem step_emb1 (c : Cfg Γf Mf.Q) (hc : ¬ Mf.IsHalting c) :
    (compTM Mf Md ι₂ ι).step (emb1 Mf Md ι₂ ι c) = emb1 Mf Md ι₂ ι (Mf.step c) := by
  have hq : ¬ (c.state = Mf.qaccept ∨ c.state = Mf.qreject) := hc
  have hnh : ¬ (compTM Mf Md ι₂ ι).IsHalting (emb1 Mf Md ι₂ ι c) := by
    simp [TM.IsHalting, emb1]
  rcases hd : Mf.δ c.state c.head with ⟨q', s', mv⟩
  have hδ : (compTM Mf Md ι₂ ι).δ (emb1 Mf Md ι₂ ι c).state (emb1 Mf Md ι₂ ι c).head =
      (Sum.inl q', s'.map Sum.inl, mv) := by
    show cδ Mf Md ι₂ ι (Sum.inl c.state) (c.head.map Sum.inl) = _
    simp only [cδ, if_neg hq, dec1_map_inl, hd]
  cases mv
  · rw [step_left _ _ _ _ hnh hδ, step_left Mf c q' s' hc hd]
    simp [emb1, getD_map_inl, List.map_tail]
  · rw [step_right _ _ _ _ hnh hδ, step_right Mf c q' s' hc hd]
    simp [emb1, getD_map_inl, List.map_tail]

theorem run_emb1 (c0 : Cfg Γf Mf.Q) : ∀ n, (∀ m < n, ¬ Mf.IsHalting (Mf.run m c0)) →
    (compTM Mf Md ι₂ ι).run n (emb1 Mf Md ι₂ ι c0) = emb1 Mf Md ι₂ ι (Mf.run n c0) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [run_succ', run_succ', ih (fun m hm => h m (by omega)),
      step_emb1 Mf Md ι₂ ι _ (h n (by omega))]

theorem init_emb1 {Sym₁ : Type} (ι₁ : Sym₁ ↪ Γf) (x : List Sym₁) :
    (compTM Mf Md ι₂ ι).init (x.map (ι₁.trans Function.Embedding.inl)) =
      emb1 Mf Md ι₂ ι (Mf.init (x.map ι₁)) := by
  cases x <;> simp [TM.init, emb1, List.map_map, Function.comp_def]

/-! Phase 2: convert the output and rewind. -/

theorem sweep (q : Mf.Q) (hq : q = Mf.qaccept ∨ q = Mf.qreject) :
    ∀ (y : List Sym₂) (A R : List (Option (Γf ⊕ Γd))) (h : Option (Γf ⊕ Γd)) (m : ℕ),
      h :: R = y.map (fun a => (some (Sum.inl (ι₂ a)) : Option (Γf ⊕ Γd))) ++
        List.replicate m none →
      ∃ m', (compTM Mf Md ι₂ ι).run y.length ⟨Sum.inl q, A, h, R⟩ =
        ⟨Sum.inl q, (y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd)))).reverse ++ A,
          none, List.replicate m' none⟩ := by
  intro y
  induction y with
  | nil =>
    intro A R h m hm
    cases m with
    | zero => simp at hm
    | succ m =>
      rw [List.replicate_succ] at hm
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨m, rfl⟩
  | cons a y ih =>
    intro A R h m hm
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at hm
    obtain ⟨rfl, hR⟩ := hm
    have hnh : ¬ (compTM Mf Md ι₂ ι).IsHalting
        ⟨Sum.inl q, A, some (Sum.inl (ι₂ a)), R⟩ := by simp [TM.IsHalting]
    rw [List.length_cons, run_succ, step_right _ _ _ _ hnh (δ_sweep_H Mf Md ι₂ ι q hq a)]
    have hR' : ∃ m'', R.headD none :: R.tail =
        y.map (fun a => (some (Sum.inl (ι₂ a)) : Option (Γf ⊕ Γd))) ++
          List.replicate m'' none := by
      cases R with
      | nil =>
        have h' := hR.symm
        simp only [List.append_eq_nil_iff, List.map_eq_nil_iff, List.replicate_eq_nil_iff] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact ⟨1, rfl⟩
      | cons r R => exact ⟨m, hR⟩
    obtain ⟨m'', hm''⟩ := hR'
    obtain ⟨m', hm'⟩ := ih _ _ _ _ hm''
    refine ⟨m', ?_⟩
    rw [hm']
    simp

theorem rewind : ∀ (u : List Sym₂) (b : Sym₂) (A R : List (Option (Γf ⊕ Γd))),
    (compTM Mf Md ι₂ ι).run (u.length + 1)
      ⟨Sum.inr (Sum.inl ()), u.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++ A,
        some (Sum.inr (ι b)), R⟩ =
      ⟨Sum.inr (Sum.inl ()), A.tail, A.headD none,
        (b :: u).reverse.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++ R⟩ := by
  intro u
  induction u with
  | nil =>
    intro b A R
    have hnh : ¬ (compTM Mf Md ι₂ ι).IsHalting
        ⟨Sum.inr (Sum.inl ()), [].map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++ A,
          some (Sum.inr (ι b)), R⟩ := by simp [TM.IsHalting]
    rw [List.length_nil, run_succ, step_left _ _ _ _ hnh (δ_rw_G Mf Md ι₂ ι (ι b))]
    rfl
  | cons c u ih =>
    intro b A R
    have hnh : ¬ (compTM Mf Md ι₂ ι).IsHalting
        ⟨Sum.inr (Sum.inl ()), (c :: u).map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++ A,
          some (Sum.inr (ι b)), R⟩ := by simp [TM.IsHalting]
    rw [List.length_cons, run_succ, step_left _ _ _ _ hnh (δ_rw_G Mf Md ι₂ ι (ι b))]
    simp only [List.map_cons, List.cons_append, List.tail_cons, List.headD_cons]
    rw [ih c A]
    simp

theorem phase2 (q : Mf.Q) (hq : q = Mf.qaccept ∨ q = Mf.qreject) (y : List Sym₂)
    (A R : List (Option (Γf ⊕ Γd))) (h : Option (Γf ⊕ Γd)) (m : ℕ)
    (hm : h :: R = y.map (fun a => (some (Sum.inl (ι₂ a)) : Option (Γf ⊕ Γd))) ++
        List.replicate m none)
    (hA : ∀ a ∈ A, dec2 a = none) :
    ∃ m', (compTM Mf Md ι₂ ι).run (y.length + 1 + y.length + 1) ⟨Sum.inl q, A, h, R⟩ =
      ⟨Sum.inr (Sum.inr Md.q₀), A.headD none :: A.tail,
        (y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++
          none :: List.replicate m' none).headD none,
        (y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++
          none :: List.replicate m' none).tail⟩ := by
  obtain ⟨m', h1⟩ := sweep Mf Md ι₂ ι q hq y A R h m hm
  refine ⟨m', ?_⟩
  have hnh1 : ¬ (compTM Mf Md ι₂ ι).IsHalting
      ⟨Sum.inl q, (y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd)))).reverse ++ A,
        none, List.replicate m' none⟩ := by simp [TM.IsHalting]
  have h2 : (compTM Mf Md ι₂ ι).run (y.length + 1) ⟨Sum.inl q, A, h, R⟩ =
      ⟨Sum.inr (Sum.inl ()),
        ((y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd)))).reverse ++ A).tail,
        ((y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd)))).reverse ++ A).headD none,
        none :: List.replicate m' none⟩ := by
    rw [run_add, h1, run_succ, step_left _ _ _ _ hnh1 (δ_sweep_none Mf Md ι₂ ι q hq)]
    rfl
  have h3 : (compTM Mf Md ι₂ ι).run y.length
      ⟨Sum.inr (Sum.inl ()),
        ((y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd)))).reverse ++ A).tail,
        ((y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd)))).reverse ++ A).headD none,
        none :: List.replicate m' none⟩ =
      ⟨Sum.inr (Sum.inl ()), A.tail, A.headD none,
        y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++
          none :: List.replicate m' none⟩ := by
    rcases hy : y.reverse with _ | ⟨b, u⟩
    · have : y = [] := List.reverse_eq_nil_iff.1 hy
      subst this
      rfl
    · have hy' : y = u.reverse ++ [b] := by
        rw [← List.reverse_reverse y, hy]; simp
      have hl : y.length = u.length + 1 := by rw [hy']; simp
      have hmr : (y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd)))).reverse =
          some (Sum.inr (ι b)) :: u.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) := by
        rw [hy']; simp
      rw [hmr, hl]
      simp only [List.cons_append, List.tail_cons, List.headD_cons]
      rw [rewind Mf Md ι₂ ι u b A]
      rw [hy']
      simp
  have hA0 : dec2 (A.headD none) = none := by
    cases A with
    | nil => rfl
    | cons a A => exact hA a List.mem_cons_self
  have hnh2 : ¬ (compTM Mf Md ι₂ ι).IsHalting
      ⟨Sum.inr (Sum.inl ()), A.tail, A.headD none,
        y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++
          none :: List.replicate m' none⟩ := by simp [TM.IsHalting]
  rw [run_succ', run_add, h2, h3,
    step_right _ _ _ _ hnh2 (δ_rw_other Mf Md ι₂ ι (A.headD none) hA0)]

/-! Phase 3: simulation of the decider, up to blank-normalisation. -/

def Rel (c : Cfg (Γf ⊕ Γd) (compTM Mf Md ι₂ ι).Q) (d : Cfg Γd Md.Q) : Prop :=
  c.state = Sum.inr (Sum.inr d.state) ∧ dec2 c.head = d.head ∧
    (∀ i, Tp c.left i = d.left.getD i none) ∧ (∀ i, Tp c.right i = d.right.getD i none)

theorem step_rel (c : Cfg (Γf ⊕ Γd) (compTM Mf Md ι₂ ι).Q) (d : Cfg Γd Md.Q)
    (h : Rel Mf Md ι₂ ι c d) :
    Rel Mf Md ι₂ ι ((compTM Mf Md ι₂ ι).step c) (Md.step d) := by
  obtain ⟨hs, hh, hl, hr⟩ := h
  by_cases hd : Md.IsHalting d
  · have hc : (compTM Mf Md ι₂ ι).IsHalting c := by
      rcases hd with h1 | h1
      · left; rw [hs, h1]
      · right; rw [hs, h1]
    rw [step_halt _ c hc, step_halt _ d hd]; exact ⟨hs, hh, hl, hr⟩
  · have hc : ¬ (compTM Mf Md ι₂ ι).IsHalting c := by
      rintro (h1 | h1) <;> apply hd
      · left; rw [hs] at h1; simpa using h1
      · right; rw [hs] at h1; simpa using h1
    rcases hδ : Md.δ d.state d.head with ⟨q', s', mv⟩
    have hδc : (compTM Mf Md ι₂ ι).δ c.state c.head = (Sum.inr (Sum.inr q'), s'.map Sum.inr, mv) := by
      rw [hs, δ_ph3, hh, hδ]
    cases mv
    · rw [step_left _ c _ _ hc hδc, step_left Md d _ _ hd hδ]
      exact ⟨rfl, Tp_headD hl, Tp_tail hl, Tp_cons (dec2_map_inr s') hr⟩
    · rw [step_right _ c _ _ hc hδc, step_right Md d _ _ hd hδ]
      exact ⟨rfl, Tp_headD hr, Tp_cons (dec2_map_inr s') hl, Tp_tail hr⟩

theorem run_rel (c : Cfg (Γf ⊕ Γd) (compTM Mf Md ι₂ ι).Q) (d : Cfg Γd Md.Q)
    (h : Rel Mf Md ι₂ ι c d) :
    ∀ n, Rel Mf Md ι₂ ι ((compTM Mf Md ι₂ ι).run n c) (Md.run n d) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => rw [run_succ', run_succ']; exact step_rel Mf Md ι₂ ι _ _ ih

theorem rel_halting (c : Cfg (Γf ⊕ Γd) (compTM Mf Md ι₂ ι).Q) (d : Cfg Γd Md.Q)
    (h : Rel Mf Md ι₂ ι c d) : (compTM Mf Md ι₂ ι).IsHalting c ↔ Md.IsHalting d := by
  unfold TM.IsHalting
  rw [h.1]
  simp

theorem rel_accept (c : Cfg (Γf ⊕ Γd) (compTM Mf Md ι₂ ι).Q) (d : Cfg Γd Md.Q)
    (h : Rel Mf Md ι₂ ι c d) : c.state = (compTM Mf Md ι₂ ι).qaccept ↔ d.state = Md.qaccept := by
  rw [h.1]
  simp

theorem init_rel (y : List Sym₂) (A : List (Option (Γf ⊕ Γd))) (hA : ∀ a ∈ A, dec2 a = none)
    (m' : ℕ) :
    Rel Mf Md ι₂ ι
      ⟨Sum.inr (Sum.inr Md.q₀), A.headD none :: A.tail,
        (y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++
          none :: List.replicate m' none).headD none,
        (y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++
          none :: List.replicate m' none).tail⟩
      (Md.init (y.map ι)) := by
  have hY : ∀ i, Tp (y.map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++
      none :: List.replicate m' none) i = ((y.map ι).map some).getD i none := by
    induction y with
    | nil =>
      intro i
      simp only [List.map_nil, List.nil_append, List.getD_nil]
      rw [← List.replicate_succ]
      exact Tp_none (fun a ha => by rw [List.eq_of_mem_replicate ha]; rfl) i
    | cons a y ih =>
      intro i
      cases i with
      | zero => simp [Tp, dec2]
      | succ i => simpa [Tp] using ih i
  have hL : ∀ i, Tp (A.headD none :: A.tail) i = ([] : List (Option Γd)).getD i none := by
    intro i
    rw [List.getD_nil]
    apply Tp_none
    cases A with
    | nil => intro a ha; simp at ha; subst ha; rfl
    | cons a0 A => intro a ha; exact hA a ha
  exact ⟨rfl, Tp_headD hY, hL, Tp_tail hY⟩

/-! The time bound. -/

def Fb (kf kd n : ℕ) : ℕ :=
  (n ^ kf + kf) + (2 * (n + (n ^ kf + kf) + 1) + 2) + ((n + (n ^ kf + kf) + 1) ^ kd + kd)

theorem key {Sym₁ : Type} (ι₁ : Sym₁ ↪ Γf) (kf kd : ℕ) (f : List Sym₁ → List Sym₂)
    (hf : ∀ x : List Sym₁, Mf.HaltsWithin (x.length ^ kf + kf) (x.map ι₁) ∧
      Mf.output (Mf.run (x.length ^ kf + kf) (Mf.init (x.map ι₁))) = (f x).map (some ∘ ι₂))
    (hhalt : ∀ w : List Sym₂, Md.HaltsWithin (w.length ^ kd + kd) (w.map ι)) (x : List Sym₁) :
    ∃ N, N ≤ Fb kf kd x.length ∧
      (compTM Mf Md ι₂ ι).HaltsWithin N (x.map (ι₁.trans Function.Embedding.inl)) ∧
      ((compTM Mf Md ι₂ ι).Accepts (x.map (ι₁.trans Function.Embedding.inl)) ↔
        Md.Accepts ((f x).map ι)) := by
  classical
  have hx := (hf x).1
  have hout := (hf x).2
  have ex : ∃ n, Mf.IsHalting (Mf.run n (Mf.init (x.map ι₁))) := ⟨_, hx⟩
  obtain ⟨n1, hcf, hmin, hn1⟩ : ∃ n1, Mf.IsHalting (Mf.run n1 (Mf.init (x.map ι₁))) ∧
      (∀ m < n1, ¬ Mf.IsHalting (Mf.run m (Mf.init (x.map ι₁)))) ∧
      n1 ≤ x.length ^ kf + kf :=
    ⟨Nat.find ex, Nat.find_spec ex, fun m hm => Nat.find_min ex hm, Nat.find_min' ex hx⟩
  have hstab := run_stable Mf _ n1 hcf _ hn1
  obtain ⟨cf, hcfdef⟩ : ∃ cf, Mf.run n1 (Mf.init (x.map ι₁)) = cf := ⟨_, rfl⟩
  rw [hstab, hcfdef] at hout
  rw [hcfdef] at hcf
  obtain ⟨m, hm⟩ := out_decomp Mf cf
  rw [hout] at hm
  have hlen : (f x).length ≤ x.length + n1 + 1 := by
    have e1 := congrArg List.length hm
    simp only [List.length_cons, List.length_append, List.length_map,
      List.length_replicate] at e1
    have e2 := run_right_length Mf (Mf.init (x.map ι₁)) n1
    rw [hcfdef] at e2
    have e3 : (Mf.init (x.map ι₁)).right.length ≤ x.length := by
      simp [TM.init]
    omega
  have hm' : cf.head.map Sum.inl :: cf.right.map (Option.map Sum.inl) =
      (f x).map (fun a => (some (Sum.inl (ι₂ a)) : Option (Γf ⊕ Γd))) ++
        List.replicate m none := by
    have := congrArg (List.map (Option.map (Sum.inl : Γf → Γf ⊕ Γd))) hm
    simpa [List.map_append, List.map_replicate, List.map_map, Function.comp_def] using this
  have hA : ∀ a ∈ cf.left.map (Option.map (Sum.inl : Γf → Γf ⊕ Γd)), dec2 a = none := by
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    cases b <;> rfl
  have h1 : (compTM Mf Md ι₂ ι).run n1
      ((compTM Mf Md ι₂ ι).init (x.map (ι₁.trans Function.Embedding.inl))) =
      ⟨Sum.inl cf.state, cf.left.map (Option.map Sum.inl), cf.head.map Sum.inl,
        cf.right.map (Option.map Sum.inl)⟩ := by
    rw [init_emb1, run_emb1 Mf Md ι₂ ι _ n1 hmin, hcfdef]
    rfl
  obtain ⟨m', h2⟩ := phase2 Mf Md ι₂ ι cf.state hcf (f x) _ _ _ m hm' hA
  have hrel0 := init_rel Mf Md ι₂ ι (f x) _ hA m'
  have hrel := run_rel Mf Md ι₂ ι _ _ hrel0 ((f x).length ^ kd + kd)
  have hdH := hhalt (f x)
  have hrun : (compTM Mf Md ι₂ ι).run
      (n1 + ((f x).length + 1 + (f x).length + 1) + ((f x).length ^ kd + kd))
      ((compTM Mf Md ι₂ ι).init (x.map (ι₁.trans Function.Embedding.inl))) =
      (compTM Mf Md ι₂ ι).run ((f x).length ^ kd + kd)
      ⟨Sum.inr (Sum.inr Md.q₀), (cf.left.map (Option.map Sum.inl)).headD none ::
          (cf.left.map (Option.map Sum.inl)).tail,
        ((f x).map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++
          none :: List.replicate m' none).headD none,
        ((f x).map (fun a => (some (Sum.inr (ι a)) : Option (Γf ⊕ Γd))) ++
          none :: List.replicate m' none).tail⟩ := by
    rw [run_add _ (n1 + ((f x).length + 1 + (f x).length + 1)) ((f x).length ^ kd + kd),
      run_add _ n1 ((f x).length + 1 + (f x).length + 1), h1, h2]
  have hH : (compTM Mf Md ι₂ ι).HaltsWithin
      (n1 + ((f x).length + 1 + (f x).length + 1) + ((f x).length ^ kd + kd))
      (x.map (ι₁.trans Function.Embedding.inl)) := by
    unfold TM.HaltsWithin
    rw [hrun]
    exact (rel_halting Mf Md ι₂ ι _ _ hrel).2 hdH
  refine ⟨_, ?_, hH, ?_⟩
  · have hy : (f x).length ≤ x.length + (x.length ^ kf + kf) + 1 := by omega
    have hT3 : (f x).length ^ kd ≤ (x.length + (x.length ^ kf + kf) + 1) ^ kd :=
      Nat.pow_le_pow_left hy kd
    unfold Fb
    omega
  · rw [accepts_iff _ _ _ hH, accepts_iff Md _ _ hdH, hrun]
    exact rel_accept Mf Md ι₂ ι _ _ hrel

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

theorem Fb_le (kf kd : ℕ) : ∃ c d, ∀ n, Fb kf kd n ≤ c * (n + 1) ^ d := by
  refine ⟨3 * (kf + 2) + 2 + (kf + 2) ^ kd + kd, (kf + 1) * (kd + 1), fun n => ?_⟩
  have hu1 : 1 ≤ n + 1 := by omega
  have e1 : n ^ kf ≤ (n + 1) ^ kf := Nat.pow_le_pow_left (by omega) _
  have e3 : (n + 1) ^ kf ≤ (n + 1) ^ (kf + 1) := Nat.pow_le_pow_right hu1 (by omega)
  have e4 : n + 1 ≤ (n + 1) ^ (kf + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hu1 (by omega)
  have e5 : 1 ≤ (n + 1) ^ (kf + 1) := Nat.one_le_pow _ _ (by omega)
  have e6 : kf ≤ kf * (n + 1) ^ (kf + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hS : n + (n ^ kf + kf) + 1 ≤ (kf + 2) * (n + 1) ^ (kf + 1) := by nlinarith
  have hD1 : (n + 1) ^ (kf + 1) ≤ (n + 1) ^ ((kf + 1) * (kd + 1)) :=
    Nat.pow_le_pow_right hu1 (by nlinarith)
  have hD2 : ((n + 1) ^ (kf + 1)) ^ kd ≤ (n + 1) ^ ((kf + 1) * (kd + 1)) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right hu1 (by nlinarith)
  have hD3 : 1 ≤ (n + 1) ^ ((kf + 1) * (kd + 1)) := Nat.one_le_pow _ _ (by omega)
  have hSk : (n + (n ^ kf + kf) + 1) ^ kd ≤ (kf + 2) ^ kd * ((n + 1) ^ (kf + 1)) ^ kd := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hS kd
  have p1 : (kf + 2) * (n + 1) ^ (kf + 1) ≤ (kf + 2) * (n + 1) ^ ((kf + 1) * (kd + 1)) :=
    Nat.mul_le_mul_left _ hD1
  have p2 : (kf + 2) ^ kd * ((n + 1) ^ (kf + 1)) ^ kd ≤
      (kf + 2) ^ kd * (n + 1) ^ ((kf + 1) * (kd + 1)) := Nat.mul_le_mul_left _ hD2
  have p3 : kd ≤ kd * (n + 1) ^ ((kf + 1) * (kd + 1)) := Nat.le_mul_of_pos_right _ (by omega)
  unfold Fb
  nlinarith

theorem main {Sym₁ Sym₂ : Type} [Fintype Sym₁] [Fintype Sym₂]
    (L₁ : Lang Sym₁) (L₂ : Lang Sym₂) (h : PolyReducible L₁ L₂) (h₂ : L₂ ∈ P Sym₂) :
    L₁ ∈ P Sym₁ := by
  obtain ⟨f, ⟨Γf, hΓf, ι₁, ι₂, Mf, kf, hf⟩, hred⟩ := h
  obtain ⟨Γd, hΓd, ι, Md, kd, hhalt, hacc⟩ := h₂
  obtain ⟨c, d, hcd⟩ := Fb_le kf kd
  obtain ⟨K, hK⟩ := poly_gen c d
  have hfin : Fintype (Γf ⊕ Γd) := by haveI := hΓf; haveI := hΓd; infer_instance
  refine ⟨Γf ⊕ Γd, hfin, ι₁.trans Function.Embedding.inl, compTM Mf Md ι₂ ι, K, ?_, ?_⟩
  · intro x
    obtain ⟨N, hN, hH, -⟩ := key Mf Md ι₂ ι ι₁ kf kd f hf hhalt x
    have hle : N ≤ x.length ^ K + K := le_trans hN (le_trans (hcd _) (hK _))
    unfold TM.HaltsWithin at hH ⊢
    rw [run_stable _ _ N hH _ hle]
    exact hH
  · intro x
    obtain ⟨N, -, -, hA⟩ := key Mf Md ι₂ ι ι₁ kf kd f hf hhalt x
    rw [hred x, hacc (f x), hA]

end CookRed

open CookPvsNP in
theorem solution {Sym₁ Sym₂ : Type} [Fintype Sym₁] [Fintype Sym₂]
    (L₁ : Lang Sym₁) (L₂ : Lang Sym₂) (h : PolyReducible L₁ L₂) (h₂ : L₂ ∈ P Sym₂) :
    L₁ ∈ P Sym₁ := by
  exact CookRed.main L₁ L₂ h h₂
