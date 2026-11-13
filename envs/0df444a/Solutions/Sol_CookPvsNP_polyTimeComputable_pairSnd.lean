-- Prove2me | solution 1 for CookPvsNP.polyTimeComputable_pairSnd
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-12T20:06:30.39805+00:00
-- url     : https://prove2.me/submissions/d4db561c-ec7b-4465-a99b-da9450fc9af0

import Mathlib
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CookPvsNP.PairSnd

open CookPvsNP

variable {A B : Type}

/-- A tape cell: `none` is the blank, `some none` the separator `#`, `some (some c)` a letter. -/
abbrev Cell (A B : Type) : Type := Option (Option (A ⊕ B))

/-- The cell holding the letter `b` of the second alphabet. -/
def cellB (b : B) : Cell A B := some (some (Sum.inr b))

/-- The cell holding the separator. -/
def sep : Cell A B := some none

/-- States: scan to the separator, check the second component, erase a malformed rest,
walk back to the separator, accept, reject. -/
inductive St
  | scan | check | erase | back | acc | rej
  deriving DecidableEq

instance : Fintype St :=
  ⟨{St.scan, St.check, St.erase, St.back, St.acc, St.rej}, fun x => by cases x <;> simp⟩

/-- The transition function. -/
def trans : St → Cell A B → St × Cell A B × Move
  | .scan, none => (.acc, none, .right)
  | .scan, some none => (.check, some none, .right)
  | .scan, some (some c) => (.scan, some (some c), .right)
  | .check, none => (.back, none, .left)
  | .check, some (some (Sum.inr b)) => (.check, some (some (Sum.inr b)), .right)
  | .check, some none => (.erase, none, .right)
  | .check, some (some (Sum.inl _)) => (.erase, none, .right)
  | .erase, none => (.back, none, .left)
  | .erase, some _ => (.erase, none, .right)
  | .back, none => (.back, none, .left)
  | .back, some (some (Sum.inr b)) => (.back, some (some (Sum.inr b)), .left)
  | .back, some none => (.acc, some none, .right)
  | .back, some (some (Sum.inl a)) => (.rej, some (some (Sum.inl a)), .right)
  | .acc, s => (.acc, s, .right)
  | .rej, s => (.rej, s, .right)

/-- The machine. -/
def M (A B : Type) : TM (Option (A ⊕ B)) where
  Q := St
  q₀ := .scan
  qaccept := .acc
  qreject := .rej
  accept_ne_reject := by decide
  δ := trans

/-- The configuration with state `q`, cells `L` to the left of the head (nearest first) and
cells `w` from the head rightwards. -/
def mk (q : St) (L w : List (Cell A B)) : Cfg (Option (A ⊕ B)) (M A B).Q :=
  { state := q, left := L, head := w.headD none, right := w.tail }

/-- Removal of trailing blanks. -/
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

theorem run_succ (n : ℕ) (c : Cfg (Option (A ⊕ B)) (M A B).Q) :
    (M A B).run (n + 1) c = (M A B).run n ((M A B).step c) := by
  simp [TM.run, Function.iterate_succ_apply]

theorem run_succ' (n : ℕ) (c : Cfg (Option (A ⊕ B)) (M A B).Q) :
    (M A B).run (n + 1) c = (M A B).step ((M A B).run n c) := by
  simp [TM.run, Function.iterate_succ_apply']

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

/-- Starting from `c`, the machine halts within `n` steps with output `out`. -/
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

/-- Cells the machine walks back over: blanks and letters of the second alphabet. -/
def OkCell (c : Cell A B) : Prop := c = none ∨ ∃ b : B, c = cellB b

/-- Walking back over a block `W` of such cells. -/
theorem back_run (W : List (Cell A B)) (hW : ∀ c ∈ W, OkCell c) (L : List (Cell A B))
    (h0 : Cell A B) (hh0 : OkCell h0) (R : List (Cell A B)) :
    (M A B).run W.length (mk .back (W ++ L) (h0 :: R)) = mk .back L (W.reverse ++ h0 :: R) := by
  induction W generalizing h0 R with
  | nil => rfl
  | cons a W ih =>
    have hs : (M A B).step (mk .back (a :: (W ++ L)) (h0 :: R)) =
        mk .back (W ++ L) (a :: h0 :: R) := by
      rcases hh0 with rfl | ⟨b, rfl⟩
      · exact step_left a (W ++ L) (none :: R) (by decide) (by decide) rfl
      · exact step_left a (W ++ L) (cellB b :: R) (by decide) (by decide) rfl
    rw [List.length_cons, run_succ, List.cons_append, hs,
      ih (fun c hc => hW c (List.mem_cons_of_mem _ hc)) a (hW a List.mem_cons_self) (h0 :: R)]
    simp

/-- From the right end of the tape, in any of the three states that turn around at a blank, the
machine walks back to the separator and accepts with the head just right of it. -/
theorem end_good (q : St) (hq : q = .check ∨ q = .erase ∨ q = .back) (W : List (Cell A B))
    (hW : ∀ c ∈ W, OkCell c) (L0 : List (Cell A B)) :
    Good (mk q (W ++ sep :: L0) []) (W.length + 2) (strip W.reverse) := by
  have hq1 : q ≠ .acc := by rcases hq with rfl | rfl | rfl <;> decide
  have hq2 : q ≠ .rej := by rcases hq with rfl | rfl | rfl <;> decide
  have hδ : trans q (([] : List (Cell A B)).headD none) = (St.back, (none : Cell A B), Move.left) := by
    rcases hq with rfl | rfl | rfl <;> rfl
  have hsep : ∀ R : List (Cell A B),
      (M A B).step (mk .back L0 (sep :: R)) = mk .acc (sep :: L0) R := fun R =>
    step_right L0 (sep :: R) (by decide) (by decide) rfl
  have hacc : ∀ R : List (Cell A B), (M A B).IsHalting (mk .acc (sep :: L0) R) := fun R =>
    Or.inl rfl
  cases W with
  | nil =>
    have s1 : (M A B).step (mk q (sep :: L0) []) = mk .back L0 (sep :: [none]) :=
      step_left sep L0 [] hq1 hq2 hδ
    refine ⟨2, by simp, ?_, ?_⟩
    · rw [run_succ, List.nil_append, s1, run_succ, hsep]; exact hacc _
    · rw [run_succ, List.nil_append, s1, run_succ, hsep]
      show (M A B).output (mk .acc (sep :: L0) [none]) = _
      rw [output_mk]
      simp [strip]
  | cons a W =>
    have s1 : (M A B).step (mk q (a :: (W ++ sep :: L0)) []) =
        mk .back (W ++ sep :: L0) (a :: [none]) :=
      step_left a (W ++ sep :: L0) [] hq1 hq2 hδ
    have ha : OkCell a := hW a List.mem_cons_self
    have hW' : ∀ c ∈ W, OkCell c := fun c hc => hW c (List.mem_cons_of_mem _ hc)
    have s2 := back_run W hW' (sep :: L0) a ha [none]
    -- the tape from the head on is now `(a :: W).reverse ++ [none]`, a nonempty list of ok cells
    have hne : ∃ (h1 : Cell A B) (R1 : List (Cell A B)), OkCell h1 ∧
        W.reverse ++ a :: [none] = h1 :: R1 := by
      cases hr : W.reverse with
      | nil => exact ⟨a, [none], ha, by simp⟩
      | cons h1 R' =>
        refine ⟨h1, R' ++ a :: [none], hW' h1 ?_, by simp⟩
        have : h1 ∈ W.reverse := by rw [hr]; exact List.mem_cons_self
        exact List.mem_reverse.mp this
    obtain ⟨h1, R1, hh1, hR⟩ := hne
    have s3 : (M A B).step (mk .back (sep :: L0) (h1 :: R1)) = mk .back L0 (sep :: h1 :: R1) := by
      rcases hh1 with rfl | ⟨b, rfl⟩
      · exact step_left sep L0 (none :: R1) (by decide) (by decide) rfl
      · exact step_left sep L0 (cellB b :: R1) (by decide) (by decide) rfl
    have hfinal : (M A B).run (W.length + 3) (mk q (a :: (W ++ sep :: L0)) []) =
        mk .acc (sep :: L0) (h1 :: R1) := by
      rw [show W.length + 3 = (W.length + 2) + 1 by omega, run_succ, s1, run_succ', run_succ', s2,
        hR, s3, hsep]
    refine ⟨W.length + 3, by simp, ?_, ?_⟩
    · rw [List.cons_append, hfinal]; exact hacc _
    · rw [List.cons_append, hfinal, output_mk, ← hR]
      rw [show W.reverse ++ a :: [none] = (a :: W).reverse ++ [none] by simp, strip_append_none]

/-- The erasing phase. -/
theorem erase_good (xs : List (Option (A ⊕ B))) (W : List (Cell A B)) (hW : ∀ c ∈ W, OkCell c)
    (L0 : List (Cell A B)) :
    Good (mk .erase (W ++ sep :: L0) (xs.map some)) (2 * xs.length + W.length + 2)
      (strip W.reverse) := by
  induction xs generalizing W with
  | nil =>
    exact (end_good .erase (Or.inr (Or.inl rfl)) W hW L0).mono (by first | omega | (simp only [List.length_cons, List.length_nil, List.length_reverse, List.length_map, List.length_append, List.length_singleton]; omega))
  | cons x xs ih =>
    have s : (M A B).step (mk .erase (W ++ sep :: L0) ((x :: xs).map some)) =
        mk .erase ((none :: W) ++ sep :: L0) (xs.map some) :=
      step_right (W ++ sep :: L0) (some x :: xs.map some) (by decide) (by decide) rfl
    have hW' : ∀ c ∈ (none :: W : List (Cell A B)), OkCell c := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inl rfl
      · exact hW c hc
    have h := ih (none :: W) hW'
    rw [List.reverse_cons, strip_append_none] at h
    exact (Good.of_step s h).mono (by first | omega | (simp only [List.length_cons, List.length_nil, List.length_reverse, List.length_map, List.length_append, List.length_singleton]; omega))

/-- The longest prefix of letters of the second alphabet. -/
def inrPrefix : List (Option (A ⊕ B)) → List B
  | some (Sum.inr b) :: xs => b :: inrPrefix xs
  | _ => []

/-- The function computed by the machine: the letters of the second alphabet that follow the
first separator, up to the first symbol that is not such a letter. -/
def g : List (Option (A ⊕ B)) → List B
  | [] => []
  | none :: xs => inrPrefix xs
  | some _ :: xs => g xs

theorem map_cellB_isSome (v : List B) : ∀ c ∈ (v.map cellB : List (Cell A B)), c.isSome := by
  intro c hc
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc
  rfl

theorem map_cellB_ok (v : List B) : ∀ c ∈ ((v.map cellB).reverse : List (Cell A B)), OkCell c := by
  intro c hc
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
  exact Or.inr ⟨b, rfl⟩

/-- The checking phase, having already read the letters `v` after the separator. -/
theorem check_good (xs : List (Option (A ⊕ B))) (v : List B) (L0 : List (Cell A B)) :
    Good (mk .check ((v.map cellB).reverse ++ sep :: L0) (xs.map some))
      (2 * xs.length + v.length + 2) ((v ++ inrPrefix xs).map cellB) := by
  induction xs generalizing v with
  | nil =>
    have h := end_good .check (Or.inl rfl) ((v.map cellB).reverse) (map_cellB_ok v) L0
    rw [List.reverse_reverse, strip_of_isSome _ (map_cellB_isSome v)] at h
    simpa [inrPrefix] using h
  | cons x xs ih =>
    -- a malformed symbol: erase the rest
    have bad : ∀ c : Cell A B,
        trans .check (some x) = (St.erase, (none : Cell A B), Move.right) →
        inrPrefix (x :: xs) = [] →
        Good (mk .check ((v.map cellB).reverse ++ sep :: L0) ((x :: xs).map some))
          (2 * (x :: xs).length + v.length + 2) ((v ++ inrPrefix (x :: xs)).map cellB) := by
      intro _ hδ hpre
      have s : (M A B).step (mk .check ((v.map cellB).reverse ++ sep :: L0) ((x :: xs).map some)) =
          mk .erase ((none :: (v.map cellB).reverse) ++ sep :: L0) (xs.map some) :=
        step_right ((v.map cellB).reverse ++ sep :: L0) (some x :: xs.map some) (by decide)
          (by decide) hδ
      have hW' : ∀ c ∈ (none :: (v.map cellB).reverse : List (Cell A B)), OkCell c := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Or.inl rfl
        · exact map_cellB_ok v c hc
      have h := erase_good xs (none :: (v.map cellB).reverse) hW' L0
      rw [List.reverse_cons, List.reverse_reverse, strip_append_none,
        strip_of_isSome _ (map_cellB_isSome v)] at h
      rw [hpre, List.append_nil]
      exact (Good.of_step s h).mono (by first | omega | (simp only [List.length_cons, List.length_nil, List.length_reverse, List.length_map, List.length_append, List.length_singleton]; omega))
    rcases x with _ | (a | b)
    · exact bad none rfl rfl
    · exact bad none rfl rfl
    · have s : (M A B).step (mk .check ((v.map cellB).reverse ++ sep :: L0)
          ((some (Sum.inr b) :: xs).map some)) =
          mk .check (((v ++ [b]).map cellB).reverse ++ sep :: L0) (xs.map some) := by
        have := step_right (q := St.check) ((v.map cellB).reverse ++ sep :: L0)
          (some (some (Sum.inr b)) :: xs.map some) (by decide) (by decide)
          (rfl : trans St.check _ = (St.check, (some (some (Sum.inr b)) : Cell A B), Move.right))
        simpa [cellB] using this
      have h := ih (v ++ [b])
      have e : (v ++ [b] ++ inrPrefix xs) = v ++ inrPrefix (some (Sum.inr b) :: xs) := by
        simp [inrPrefix]
      rw [e] at h
      exact (Good.of_step s h).mono (by first | omega | (simp only [List.length_cons, List.length_nil, List.length_reverse, List.length_map, List.length_append, List.length_singleton]; omega))

/-- The scanning phase: the whole computation. -/
theorem scan_good (x : List (Option (A ⊕ B))) (L : List (Cell A B)) :
    Good (mk .scan L (x.map some)) (2 * x.length + 3) ((g x).map cellB) := by
  induction x generalizing L with
  | nil =>
    have s : (M A B).step (mk .scan L []) = mk .acc (none :: L) [] :=
      step_right L [] (by decide) (by decide) rfl
    refine ⟨1, by simp, ?_, ?_⟩
    · rw [run_succ, List.map_nil, s]; exact Or.inl rfl
    · rw [run_succ, List.map_nil, s]
      show (M A B).output (mk .acc (none :: L) []) = _
      rw [output_mk]
      simp [strip, g]
  | cons y x ih =>
    rcases y with _ | c
    · have s : (M A B).step (mk .scan L ((none :: x).map some)) =
          mk .check ((([] : List B).map cellB).reverse ++ sep :: L) (x.map some) :=
        step_right L (some none :: x.map some) (by decide) (by decide) rfl
      have h := check_good x [] L
      simp only [List.nil_append, List.length_nil] at h
      exact (Good.of_step s h).mono (by first | omega | (simp only [List.length_cons, List.length_nil, List.length_reverse, List.length_map, List.length_append, List.length_singleton]; omega))
    · have s : (M A B).step (mk .scan L ((some c :: x).map some)) =
          mk .scan (some (some c) :: L) (x.map some) :=
        step_right L (some (some c) :: x.map some) (by decide) (by decide) rfl
      have h := ih (some (some c) :: L)
      exact (Good.of_step s h).mono (by first | omega | (simp only [List.length_cons, List.length_nil, List.length_reverse, List.length_map, List.length_append, List.length_singleton]; omega))

theorem bound (n : ℕ) : 2 * n + 3 ≤ n ^ 4 + 4 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num
  · have h1 : 2 * n ≤ n * n := Nat.mul_le_mul_right n h
    have h2 : n * n ≤ n ^ 4 := by
      calc n * n = n ^ 2 := by ring
        _ ≤ n ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

theorem inrPrefix_map (t : List B) :
    inrPrefix (t.map (some ∘ Sum.inr) : List (Option (A ⊕ B))) = t := by
  induction t with
  | nil => rfl
  | cons b t ih => simp [inrPrefix, ih]

theorem g_pair (s : List A) (t : List B) :
    g (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)) = t := by
  induction s with
  | nil => simp [g, inrPrefix_map]
  | cons a s ih => simpa [g] using ih

end CookPvsNP.PairSnd

open CookPvsNP in
theorem solution (A B : Type) [Fintype A] [Fintype B] :
    ∃ g : List (Option (A ⊕ B)) → List B, PolyTimeComputable g ∧
      ∀ (s : List A) (t : List B),
        g (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)) = t := by
  refine ⟨PairSnd.g, ?_, PairSnd.g_pair⟩
  refine ⟨Option (A ⊕ B), inferInstance, Function.Embedding.refl _,
    ⟨fun b => some (Sum.inr b), fun b b' h => by simpa using h⟩, PairSnd.M A B, 4, ?_⟩
  intro x
  obtain ⟨m, hm, hhalt, hout⟩ := PairSnd.scan_good x ([] : List (PairSnd.Cell A B))
  have hN : m ≤ x.length ^ 4 + 4 := le_trans hm (PairSnd.bound x.length)
  have hrun := PairSnd.run_mono _ hhalt hN
  have hinit : (PairSnd.M A B).init (x.map (Function.Embedding.refl (Option (A ⊕ B)))) =
      PairSnd.mk .scan [] (x.map some) := by
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
