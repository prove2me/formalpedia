-- Prove2me | solution 1 for CookPvsNP.polyTimeComputable_pairFst
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T01:19:03.873869+00:00
-- url     : https://prove2.me/submissions/4490fdf6-c4e6-4f09-8268-4d1f2ff3b784

import Mathlib
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CookPvsNP.PairFst

open CookPvsNP

variable {A B : Type}

abbrev Cell (A B : Type) : Type := Option (Option (A ⊕ B))

def cellA (a : A) : Cell A B := some (some (Sum.inl a))

inductive St
  | scan | toEnd | eraseBack | backL | acc | rej
  deriving DecidableEq

instance : Fintype St :=
  ⟨{St.scan, St.toEnd, St.eraseBack, St.backL, St.acc, St.rej}, fun x => by cases x <;> simp⟩

def trans : St → Cell A B → St × Cell A B × Move
  | .scan, some (some (Sum.inl a)) => (.scan, some (some (Sum.inl a)), .right)
  | .scan, none => (.backL, none, .left)
  | .scan, some _ => (.toEnd, none, .right)
  | .toEnd, none => (.eraseBack, none, .left)
  | .toEnd, some c => (.toEnd, some c, .right)
  | .eraseBack, none => (.backL, none, .left)
  | .eraseBack, some _ => (.eraseBack, none, .left)
  | .backL, none => (.acc, none, .right)
  | .backL, some c => (.backL, some c, .left)
  | .acc, s => (.acc, s, .right)
  | .rej, s => (.rej, s, .right)

def M (A B : Type) : TM (Option (A ⊕ B)) where
  Q := St
  q₀ := .scan
  qaccept := .acc
  qreject := .rej
  accept_ne_reject := by decide
  δ := trans

def mk (q : St) (L w : List (Cell A B)) : Cfg (Option (A ⊕ B)) (M A B).Q :=
  { state := q, left := L, head := w.headD none, right := w.tail }

def strip (l : List (Cell A B)) : List (Cell A B) :=
  (l.reverse.dropWhile Option.isNone).reverse

theorem output_mk (q : St) (L w : List (Cell A B)) : (M A B).output (mk q L w) = strip w := by
  cases w with
  | nil => simp [TM.output, mk, strip]
  | cons c w => simp [TM.output, mk, strip]

theorem strip_append_none (l : List (Cell A B)) : strip (l ++ [none]) = strip l := by
  simp [strip]

theorem strip_of_isSome (l : List (Cell A B)) (h : ∀ c ∈ l, c.isSome) : strip l = l := by
  unfold strip
  rcases List.eq_nil_or_concat l with rfl | ⟨l', c, rfl⟩
  · simp
  · have hc : c.isSome := h c (by simp)
    cases c with
    | none => simp at hc
    | some c => simp

theorem strip_append_replicate (l : List (Cell A B)) (k : ℕ) :
    strip (l ++ List.replicate k none) = strip l := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ', ← List.append_assoc, strip_append_none, ih]

theorem strip_blanks (P : List A) (k : ℕ) :
    strip ((P.map cellA : List (Cell A B)) ++ none :: List.replicate k none) = P.map cellA := by
  have e : ((P.map cellA : List (Cell A B)) ++ none :: List.replicate k none) =
      P.map cellA ++ List.replicate (k + 1) none := by simp [List.replicate_succ]
  rw [e, strip_append_replicate, strip_of_isSome]
  intro c hc
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hc
  rfl

theorem not_halting {q : St} (h1 : q ≠ .acc) (h2 : q ≠ .rej) (L w : List (Cell A B)) :
    ¬ (M A B).IsHalting (mk q L w) := by
  intro h
  rcases h with h | h
  · exact h1 h
  · exact h2 h

theorem step_right {q q' : St} {c' : Cell A B} (L w : List (Cell A B)) (h1 : q ≠ .acc)
    (h2 : q ≠ .rej) (hδ : trans q (w.headD none) = (q', c', Move.right)) :
    (M A B).step (mk q L w) = mk q' (c' :: L) w.tail := by
  unfold TM.step
  rw [if_neg (not_halting h1 h2 L w)]
  have h : (M A B).δ (mk q L w).state (mk q L w).head = (q', c', Move.right) := hδ
  simp only [h]
  rfl

theorem step_left {q q' : St} {c' : Cell A B} (a : Cell A B) (L w : List (Cell A B))
    (h1 : q ≠ .acc) (h2 : q ≠ .rej) (hδ : trans q (w.headD none) = (q', c', Move.left)) :
    (M A B).step (mk q (a :: L) w) = mk q' L (a :: c' :: w.tail) := by
  unfold TM.step
  rw [if_neg (not_halting h1 h2 (a :: L) w)]
  have h : (M A B).δ (mk q (a :: L) w).state (mk q (a :: L) w).head = (q', c', Move.left) := hδ
  simp only [h]
  rfl

theorem step_left_nil {q q' : St} {c' : Cell A B} (w : List (Cell A B))
    (h1 : q ≠ .acc) (h2 : q ≠ .rej) (hδ : trans q (w.headD none) = (q', c', Move.left)) :
    (M A B).step (mk q [] w) = mk q' [] (none :: c' :: w.tail) := by
  unfold TM.step
  rw [if_neg (not_halting h1 h2 [] w)]
  have h : (M A B).δ (mk q [] w).state (mk q [] w).head = (q', c', Move.left) := hδ
  simp only [h]
  rfl

theorem run_succ (n : ℕ) (c : Cfg (Option (A ⊕ B)) (M A B).Q) :
    (M A B).run (n + 1) c = (M A B).run n ((M A B).step c) := by
  simp [TM.run, Function.iterate_succ_apply]

theorem run_halting (n : ℕ) (c : Cfg (Option (A ⊕ B)) (M A B).Q) (h : (M A B).IsHalting c) :
    (M A B).run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : (M A B).step c = c := by
      unfold TM.step
      rw [if_pos h]
    rw [run_succ, hs, ih]

theorem run_mono {n N : ℕ} (c : Cfg (Option (A ⊕ B)) (M A B).Q)
    (h : (M A B).IsHalting ((M A B).run n c)) (hN : n ≤ N) :
    (M A B).run N c = (M A B).run n c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  have e : (M A B).run (n + d) c = (M A B).run d ((M A B).run n c) := by
    simp [TM.run, Nat.add_comm n d, Function.iterate_add_apply]
  rw [e, run_halting _ _ h]

def Good (c : Cfg (Option (A ⊕ B)) (M A B).Q) (n : ℕ) (out : List (Cell A B)) : Prop :=
  ∃ m, m ≤ n ∧ (M A B).IsHalting ((M A B).run m c) ∧ (M A B).output ((M A B).run m c) = out

theorem Good.of_step {c c' : Cfg (Option (A ⊕ B)) (M A B).Q} (h : (M A B).step c = c')
    {n : ℕ} {out : List (Cell A B)} (hg : Good c' n out) : Good c (n + 1) out := by
  obtain ⟨m, hm, h1, h2⟩ := hg
  refine ⟨m + 1, by omega, ?_, ?_⟩
  · rw [run_succ, h]; exact h1
  · rw [run_succ, h]; exact h2

theorem Good.mono {c : Cfg (Option (A ⊕ B)) (M A B).Q} {n n' : ℕ} {out : List (Cell A B)}
    (hg : Good c n out) (h : n ≤ n') : Good c n' out := by
  obtain ⟨m, hm, h1, h2⟩ := hg
  exact ⟨m, by omega, h1, h2⟩


/-- Walking left over the prefix letters, then accepting. -/
theorem backL_good (L : List A) (b : A) (R : List (Cell A B)) :
    Good (mk .backL (L.map cellA) (cellA b :: R)) (L.length + 2)
      (strip (L.reverse.map cellA ++ cellA b :: R)) := by
  induction L generalizing b R with
  | nil =>
    have s1 : (M A B).step (mk .backL [] (cellA b :: R)) = mk .backL [] (none :: cellA b :: R) :=
      step_left_nil (cellA b :: R) (by decide) (by decide) rfl
    have s2 : (M A B).step (mk .backL [] (none :: cellA b :: R)) =
        mk .acc [none] (cellA b :: R) :=
      step_right [] (none :: cellA b :: R) (by decide) (by decide) rfl
    refine ⟨2, by simp, ?_, ?_⟩
    · rw [run_succ, List.map_nil, s1, run_succ, s2]; exact Or.inl rfl
    · rw [run_succ, List.map_nil, s1, run_succ, s2]
      show (M A B).output (mk .acc [none] (cellA b :: R)) = _
      rw [output_mk]
      simp
  | cons a L ih =>
    have s : (M A B).step (mk .backL (cellA a :: L.map cellA) (cellA b :: R)) =
        mk .backL (L.map cellA) (cellA a :: cellA b :: R) :=
      step_left (cellA a) (L.map cellA) (cellA b :: R) (by decide) (by decide) rfl
    have h := ih a (cellA b :: R)
    have e : (L.reverse.map cellA ++ cellA a :: cellA b :: R : List (Cell A B)) =
        (a :: L).reverse.map cellA ++ cellA b :: R := by simp
    rw [e] at h
    exact (Good.of_step s h).mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))

theorem enter_backL (q : St) (hq : q = .scan ∨ q = .eraseBack) (L : List A) (k : ℕ) :
    Good (mk q (L.map cellA) (none :: List.replicate k none)) (L.length + 2)
      (L.reverse.map cellA : List (Cell A B)) := by
  have hq1 : q ≠ .acc := by rcases hq with rfl | rfl <;> decide
  have hq2 : q ≠ .rej := by rcases hq with rfl | rfl <;> decide
  have hδ : trans q (((none : Cell A B) :: List.replicate k none).headD none) =
      (St.backL, (none : Cell A B), Move.left) := by
    rcases hq with rfl | rfl <;> rfl
  cases L with
  | nil =>
    have s1 : (M A B).step (mk q [] (none :: List.replicate k none)) =
        mk .backL [] (none :: none :: List.replicate k none) :=
      step_left_nil (none :: List.replicate k none) hq1 hq2 hδ
    have s2 : (M A B).step (mk .backL [] (none :: none :: List.replicate k none)) =
        mk .acc [none] (none :: List.replicate k none) :=
      step_right [] (none :: none :: List.replicate k none) (by decide) (by decide) rfl
    refine ⟨2, by simp, ?_, ?_⟩
    · rw [run_succ, List.map_nil, s1, run_succ, s2]; exact Or.inl rfl
    · rw [run_succ, List.map_nil, s1, run_succ, s2]
      show (M A B).output (mk .acc [none] (none :: List.replicate k none)) = _
      rw [output_mk]
      exact strip_blanks [] k
  | cons a L =>
    have s1 : (M A B).step (mk q (cellA a :: L.map cellA) (none :: List.replicate k none)) =
        mk .backL (L.map cellA) (cellA a :: none :: List.replicate k none) :=
      step_left (cellA a) (L.map cellA) (none :: List.replicate k none) hq1 hq2 hδ
    have h := backL_good (B := B) L a (none :: List.replicate k none)
    have e : (L.reverse.map cellA ++ cellA a :: none :: List.replicate k none : List (Cell A B)) =
        (L.reverse ++ [a]).map cellA ++ none :: List.replicate k none := by simp
    rw [e, strip_blanks] at h
    rw [List.reverse_cons]
    exact (Good.of_step s1 h).mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))

theorem eraseBack_good (L : List A) (W : List (Option (A ⊕ B))) (y : Option (A ⊕ B)) (k : ℕ) :
    Good (mk .eraseBack (W.map some ++ none :: L.map cellA) (some y :: List.replicate k none))
      (W.length + L.length + 3) (L.reverse.map cellA : List (Cell A B)) := by
  induction W generalizing y k with
  | nil =>
    have s : (M A B).step (mk .eraseBack (none :: L.map cellA) (some y :: List.replicate k none)) =
        mk .eraseBack (L.map cellA) (none :: List.replicate (k + 1) none) :=
      step_left none (L.map cellA) (some y :: List.replicate k none) (by decide) (by decide) rfl
    have h := enter_backL (B := B) .eraseBack (Or.inr rfl) L (k + 1)
    exact (Good.of_step s h).mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))
  | cons w W ih =>
    have s : (M A B).step (mk .eraseBack (some w :: (W.map some ++ none :: L.map cellA))
        (some y :: List.replicate k none)) =
        mk .eraseBack (W.map some ++ none :: L.map cellA) (some w :: List.replicate (k + 1) none) :=
      step_left (some w) (W.map some ++ none :: L.map cellA) (some y :: List.replicate k none)
        (by decide) (by decide) rfl
    have h := ih w (k + 1)
    exact (Good.of_step s h).mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))

theorem toEnd_good (L : List A) (x W : List (Option (A ⊕ B))) :
    Good (mk .toEnd (W.map some ++ none :: L.map cellA) (x.map some))
      (2 * x.length + W.length + L.length + 3) (L.reverse.map cellA : List (Cell A B)) := by
  induction x generalizing W with
  | nil =>
    cases W with
    | nil =>
      have s : (M A B).step (mk .toEnd (none :: L.map cellA) []) =
          mk .eraseBack (L.map cellA) (none :: List.replicate 1 none) :=
        step_left none (L.map cellA) [] (by decide) (by decide) rfl
      have h := enter_backL (B := B) .eraseBack (Or.inr rfl) L 1
      exact (Good.of_step s h).mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))
    | cons w W =>
      have s : (M A B).step (mk .toEnd (some w :: (W.map some ++ none :: L.map cellA)) []) =
          mk .eraseBack (W.map some ++ none :: L.map cellA) (some w :: List.replicate 1 none) :=
        step_left (some w) (W.map some ++ none :: L.map cellA) [] (by decide) (by decide) rfl
      have h := eraseBack_good L W w 1
      exact (Good.of_step s h).mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))
  | cons y x ih =>
    have s : (M A B).step (mk .toEnd (W.map some ++ none :: L.map cellA) (some y :: x.map some)) =
        mk .toEnd ((y :: W).map some ++ none :: L.map cellA) (x.map some) :=
      step_right (W.map some ++ none :: L.map cellA) (some y :: x.map some) (by decide)
        (by decide) rfl
    have h := ih (y :: W)
    exact (Good.of_step s h).mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))

/-- The longest prefix of letters of the first alphabet. -/
def g : List (Option (A ⊕ B)) → List A
  | some (Sum.inl a) :: xs => a :: g xs
  | _ => []

theorem scan_good (x : List (Option (A ⊕ B))) (L : List A) :
    Good (mk .scan (L.map cellA) (x.map some)) (2 * x.length + L.length + 4)
      ((L.reverse ++ g x).map cellA : List (Cell A B)) := by
  induction x generalizing L with
  | nil =>
    have h := enter_backL (B := B) .scan (Or.inl rfl) L 0
    have e : ((L.reverse ++ g ([] : List (Option (A ⊕ B)))).map cellA : List (Cell A B)) =
        L.reverse.map cellA := by simp [g]
    rw [e]
    exact h.mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))
  | cons y x ih =>
    have other : ∀ y' : Option (A ⊕ B), (∀ a, y' ≠ some (Sum.inl a)) →
        trans .scan (some y') = (St.toEnd, (none : Cell A B), Move.right) →
        g (y' :: x) = [] →
        Good (mk .scan (L.map cellA) ((y' :: x).map some)) (2 * (y' :: x).length + L.length + 4)
          ((L.reverse ++ g (y' :: x)).map cellA : List (Cell A B)) := by
      intro y' _ hδ hg
      have s : (M A B).step (mk .scan (L.map cellA) (some y' :: x.map some)) =
          mk .toEnd (([] : List (Option (A ⊕ B))).map some ++ none :: L.map cellA) (x.map some) :=
        step_right (L.map cellA) (some y' :: x.map some) (by decide) (by decide) hδ
      have h := toEnd_good L x []
      rw [hg, List.append_nil]
      exact (Good.of_step s h).mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))
    rcases y with _ | (a | b)
    · exact other none (by simp) rfl (by simp [g])
    · have s : (M A B).step (mk .scan (L.map cellA) (some (some (Sum.inl a)) :: x.map some)) =
          mk .scan (cellA a :: L.map cellA) (x.map some) :=
        step_right (L.map cellA) (some (some (Sum.inl a)) :: x.map some) (by decide) (by decide) rfl
      have h := ih (a :: L)
      have e : ((a :: L).reverse ++ g x) = L.reverse ++ g (some (Sum.inl a) :: x) := by
        simp [g]
      rw [e] at h
      exact (Good.of_step s h).mono (by (first | omega | (simp only [List.length_cons, List.length_nil, List.length_map, List.length_append, List.length_reverse] at *; omega) | simp))
    · exact other (some (Sum.inr b)) (by simp) rfl (by simp [g])

theorem bound (n : ℕ) : 2 * n + 4 ≤ n ^ 6 + 6 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num
  · have h1 : 2 * n ≤ n * n := Nat.mul_le_mul_right n h
    have h2 : n * n ≤ n ^ 6 := by
      calc n * n = n ^ 2 := by ring
        _ ≤ n ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

theorem g_pair (s : List A) (t : List B) :
    g (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)) = s := by
  induction s with
  | nil => simp [g]
  | cons a s ih => simpa [g] using ih

end CookPvsNP.PairFst

open CookPvsNP in
theorem solution (A B : Type) [Fintype A] [Fintype B] :
    ∃ g : List (Option (A ⊕ B)) → List A, CookPvsNP.PolyTimeComputable g ∧
      ∀ (s : List A) (t : List B),
        g (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)) = s := by
  refine ⟨PairFst.g, ?_, PairFst.g_pair⟩
  refine ⟨Option (A ⊕ B), inferInstance, Function.Embedding.refl _,
    ⟨fun a => some (Sum.inl a), fun a a' h => by simpa using h⟩, PairFst.M A B, 6, ?_⟩
  intro x
  have hg := PairFst.scan_good (B := B) x []
  simp only [List.reverse_nil, List.nil_append, List.length_nil, List.map_nil,
    Nat.add_zero] at hg
  obtain ⟨m, hm, hhalt, hout⟩ := hg
  have hN : m ≤ x.length ^ 6 + 6 := le_trans hm (PairFst.bound x.length)
  have hrun := PairFst.run_mono _ hhalt hN
  have hinit : (PairFst.M A B).init (x.map (Function.Embedding.refl (Option (A ⊕ B)))) =
      PairFst.mk .scan [] (x.map some) := by
    have e : (⇑(Function.Embedding.refl (Option (A ⊕ B))) : Option (A ⊕ B) → Option (A ⊕ B)) = id :=
      rfl
    rw [e, List.map_id]
    rfl
  constructor
  · unfold TM.HaltsWithin
    rw [hinit, hrun]
    exact hhalt
  · rw [hinit, hrun, hout]
    rfl

