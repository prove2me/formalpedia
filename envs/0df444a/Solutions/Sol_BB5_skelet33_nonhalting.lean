-- Prove2me | solution 1 for BB5.skelet33_nonhalting
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-22T22:39:31.358946+00:00
-- url     : https://prove2.me/submissions/340c7292-a601-46ec-b629-21c5437249ea

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet33

namespace SK
open FCP.BusyBeaver

/-! ## Layer 1: half-tape configurations -/

/-- One half of the tape, read outward from the head (index `0` is the adjacent cell). -/
def Side := ℕ → Bool

def cons (b : Bool) (s : Side) : Side := fun n => match n with
  | 0 => b
  | n + 1 => s n

def tl (s : Side) : Side := fun n => s (n + 1)

def zeros : Side := fun _ => false

theorem cons_tl (s : Side) : cons (s 0) (tl s) = s := by
  funext n; cases n <;> rfl

theorem cons_zeros : cons false zeros = zeros := by
  funext n; cases n <;> rfl

/-- A configuration: state, left side, scanned symbol, right side. -/
structure SC where
  q : Fin 5
  l : Side
  h : Bool
  r : Side

def stepS (M : TM 5) (c : SC) : Option SC :=
  match M.trans c.q c.h with
  | (_, _, none) => none
  | (w, true, some q') => some ⟨q', cons w c.l, c.r 0, tl c.r⟩
  | (w, false, some q') => some ⟨q', tl c.l, c.l 0, cons w c.r⟩

def runS (M : TM 5) (c : SC) : ℕ → Option SC
  | 0 => some c
  | t + 1 => (runS M c t).bind (stepS M)

/-- `c` is the configuration `s` seen from the head. -/
def Rep (c : Config 5) (s : SC) : Prop :=
  c.state = s.q ∧ c.tape c.head = s.h ∧ (∀ n : ℕ, c.tape (c.head - 1 - n) = s.l n) ∧
    (∀ n : ℕ, c.tape (c.head + 1 + n) = s.r n)

theorem rep_step (M : TM 5) (c : Config 5) (s : SC) (hr : Rep c s) :
    (step M c = none ∧ stepS M s = none) ∨
      ∃ c' s', step M c = some c' ∧ stepS M s = some s' ∧ Rep c' s' := by
  obtain ⟨hq, hh, hl, hrr⟩ := hr
  have hb : c.tape c.head = s.h := hh
  unfold step stepS
  rw [hq, hb]
  generalize M.trans s.q s.h = x
  obtain ⟨w, d, o⟩ := x
  cases o with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some q' =>
    right
    cases d
    · refine ⟨_, _, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show Function.update c.tape c.head w (c.head - 1) = s.l 0
        rw [Function.update_apply, if_neg (by omega)]
        have := hl 0; simpa using this
      · intro n
        show Function.update c.tape c.head w (c.head - 1 - 1 - n) = s.l (n + 1)
        rw [Function.update_apply, if_neg (by omega)]
        have := hl (n + 1)
        rw [show c.head - 1 - ((n + 1 : ℕ) : ℤ) = c.head - 1 - 1 - n by omega] at this
        exact this
      · intro n
        show Function.update c.tape c.head w (c.head - 1 + 1 + n) = cons w s.r n
        rw [Function.update_apply]
        cases n with
        | zero => rw [if_pos (by omega)]; rfl
        | succ n =>
          rw [if_neg (by omega)]
          have := hrr n
          rw [show c.head - 1 + 1 + ((n + 1 : ℕ) : ℤ) = c.head + 1 + n by omega]
          exact this
    · refine ⟨_, _, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · show Function.update c.tape c.head w (c.head + 1) = s.r 0
        rw [Function.update_apply, if_neg (by omega)]
        have := hrr 0; simpa using this
      · intro n
        show Function.update c.tape c.head w (c.head + 1 - 1 - n) = cons w s.l n
        rw [Function.update_apply]
        cases n with
        | zero => rw [if_pos (by omega)]; rfl
        | succ n =>
          rw [if_neg (by omega)]
          have := hl n
          rw [show c.head + 1 - 1 - ((n + 1 : ℕ) : ℤ) = c.head - 1 - n by omega]
          exact this
      · intro n
        show Function.update c.tape c.head w (c.head + 1 + 1 + n) = s.r (n + 1)
        rw [Function.update_apply, if_neg (by omega)]
        have := hrr (n + 1)
        rw [show c.head + 1 + ((n + 1 : ℕ) : ℤ) = c.head + 1 + 1 + n by omega] at this
        exact this

theorem rep_run (M : TM 5) (c : Config 5) (s : SC) (hr : Rep c s) : ∀ t : ℕ,
    (run M c t = none ∧ runS M s t = none) ∨
      ∃ c' s', run M c t = some c' ∧ runS M s t = some s' ∧ Rep c' s' := by
  intro t
  induction t with
  | zero => exact Or.inr ⟨c, s, rfl, rfl, hr⟩
  | succ t ih =>
    rcases ih with ⟨h1, h2⟩ | ⟨c', s', h1, h2, h3⟩
    · left; constructor
      · show (run M c t).bind (step M) = none; rw [h1]; rfl
      · show (runS M s t).bind (stepS M) = none; rw [h2]; rfl
    · rcases rep_step M c' s' h3 with ⟨g1, g2⟩ | ⟨c'', s'', g1, g2, g3⟩
      · left; constructor
        · show (run M c t).bind (step M) = none; rw [h1]; exact g1
        · show (runS M s t).bind (stepS M) = none; rw [h2]; exact g2
      · right; refine ⟨c'', s'', ?_, ?_, g3⟩
        · show (run M c t).bind (step M) = _; rw [h1]; exact g1
        · show (runS M s t).bind (stepS M) = _; rw [h2]; exact g2

/-- Non-halting transfers from the half-tape model. -/
theorem nonhalt_of_S (M : TM 5) (c : Config 5) (s : SC) (hr : Rep c s)
    (h : ∀ t, runS M s t ≠ none) : ∀ t, run M c t ≠ none := by
  intro t ht
  rcases rep_run M c s hr t with ⟨_, h2⟩ | ⟨c', s', h1, _, _⟩
  · exact h t h2
  · rw [h1] at ht; exact Option.some_ne_none _ ht

theorem rep_init : Rep (init (n := 5) (by omega)) ⟨0, zeros, false, zeros⟩ :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-! ### Reachability -/

/-- `Reach M s s'`: `s'` is reached from `s` in some number of steps. -/
def Reach (M : TM 5) (s s' : SC) : Prop := ∃ n, runS M s n = some s'
/-- `Prog M s s'`: reached in at least one step. -/
def Prog (M : TM 5) (s s' : SC) : Prop := ∃ n, 0 < n ∧ runS M s n = some s'

theorem runS_trans (M : TM 5) (c d : SC) (a : ℕ) (h : runS M c a = some d) :
    ∀ b : ℕ, runS M c (a + b) = runS M d b := by
  intro b
  induction b with
  | zero => exact h
  | succ b ih =>
    show (runS M c (a + b)).bind (stepS M) = (runS M d b).bind (stepS M)
    rw [ih]

theorem runS_none (M : TM 5) (c : SC) (s : ℕ) (h : runS M c s = none) :
    ∀ m : ℕ, runS M c (s + m) = none := by
  intro m
  induction m with
  | zero => exact h
  | succ m ih =>
    show (runS M c (s + m)).bind (stepS M) = none
    rw [ih]; rfl

theorem Reach.refl (M : TM 5) (s : SC) : Reach M s s := ⟨0, rfl⟩

theorem Reach.trans {M : TM 5} {a b c : SC} (h1 : Reach M a b) (h2 : Reach M b c) : Reach M a c := by
  obtain ⟨n, hn⟩ := h1; obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, by rw [runS_trans M a b n hn m]; exact hm⟩

theorem Reach.step {M : TM 5} {a b c : SC} (h1 : stepS M a = some b) (h2 : Reach M b c) : Reach M a c := by
  obtain ⟨m, hm⟩ := h2
  exact ⟨1 + m, by rw [runS_trans M a b 1 h1 m]; exact hm⟩

theorem Reach.of_eq {M : TM 5} {a b : SC} (h : a = b) : Reach M a b := h ▸ Reach.refl M a

theorem Prog.step {M : TM 5} {a b c : SC} (h1 : stepS M a = some b) (h2 : Reach M b c) : Prog M a c := by
  obtain ⟨m, hm⟩ := h2
  exact ⟨1 + m, by omega, by rw [runS_trans M a b 1 h1 m]; exact hm⟩

theorem Prog.trans_reach {M : TM 5} {a b c : SC} (h1 : Prog M a b) (h2 : Reach M b c) : Prog M a c := by
  obtain ⟨n, hn0, hn⟩ := h1; obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, by omega, by rw [runS_trans M a b n hn m]; exact hm⟩

theorem Reach.trans_prog {M : TM 5} {a b c : SC} (h1 : Reach M a b) (h2 : Prog M b c) : Prog M a c := by
  obtain ⟨n, hn⟩ := h1; obtain ⟨m, hm0, hm⟩ := h2
  exact ⟨n + m, by omega, by rw [runS_trans M a b n hn m]; exact hm⟩

theorem Prog.reach {M : TM 5} {a b : SC} (h : Prog M a b) : Reach M a b :=
  let ⟨n, _, hn⟩ := h; ⟨n, hn⟩

/-- A configuration that always makes progress to another such configuration never halts. -/
theorem nonhalt_cond {ι : Type} (M : TM 5) (C : ι → SC) (P : ι → Prop)
    (hP : ∀ i, P i → ∃ j, Prog M (C i) (C j) ∧ P j) :
    ∀ t i, P i → runS M (C i) t ≠ none := by
  intro t
  refine Nat.strongRecOn t ?_
  intro t ih
  intro i hi ht
  obtain ⟨j, ⟨n, hn0, hn⟩, hj⟩ := hP i hi
  by_cases htn : t < n
  · have := runS_none M (C i) t ht (n - t)
    rw [show t + (n - t) = n by omega, hn] at this
    exact Option.some_ne_none _ this
  · have := runS_trans M (C i) (C j) n hn (t - n)
    rw [show n + (t - n) = t by omega, ht] at this
    exact ih (t - n) (by omega) j hj this.symm

theorem nonhalt_of_reach {M : TM 5} {a b : SC} (h : Reach M a b) (hb : ∀ t, runS M b t ≠ none) :
    ∀ t, runS M a t ≠ none := by
  obtain ⟨n, hn⟩ := h
  intro t ht
  by_cases htn : t < n
  · have := runS_none M a t ht (n - t)
    rw [show t + (n - t) = n by omega, hn] at this
    exact Option.some_ne_none _ this
  · have := runS_trans M a b n hn (t - n)
    rw [show n + (t - n) = t by omega, ht] at this
    exact hb (t - n) this.symm

end SK
namespace SK
open FCP.BusyBeaver

/-! ## Layer 2: the binary tapes and the function `b` -/

/-- `L n`: the counter `n` in base 2, least significant bit nearest the head, each bit as `b000`
(read outward: `0 0 0 b`). -/
def L : ℕ → Side
  | 0 => zeros
  | n + 1 => cons false (cons false (cons false (cons ((n + 1) % 2 == 1) (L ((n + 1) / 2)))))
decreasing_by omega

/-- `R m`: the counter `m ≥ 1` in base 2, each bit as `1b` (read outward). -/
def R : ℕ → Side
  | 0 => zeros
  | m + 1 => cons true (cons ((m + 1) % 2 == 1) (R ((m + 1) / 2)))
decreasing_by omega

theorem L_zero : L 0 = zeros := by rw [L]

theorem L_even (n : ℕ) (h : 0 < n) :
    L (2 * n) = cons false (cons false (cons false (cons false (L n)))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, L]
  rw [show (2 * k + 1 + 1) % 2 = 0 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega]; rfl

theorem L_odd (n : ℕ) :
    L (2 * n + 1) = cons false (cons false (cons false (cons true (L n)))) := by
  rw [L, show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega]; rfl

theorem R_even (m : ℕ) (h : 0 < m) : R (2 * m) = cons true (cons false (R m)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, R]
  rw [show (2 * k + 1 + 1) % 2 = 0 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega]; rfl

theorem R_odd (m : ℕ) : R (2 * m + 1) = cons true (cons true (R m)) := by
  rw [R, show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega]; rfl

theorem R_zero : R 0 = zeros := by rw [R]

theorem L_head (n : ℕ) : L n 0 = false := by
  cases n with
  | zero => rw [L_zero]; rfl
  | succ n => rw [L]; rfl

/-- `K n` is `L n` without its innermost `0`. -/
def K (n : ℕ) : Side := tl (L n)
/-- `J n` is `L n` without its three innermost `0`s. -/
def J (n : ℕ) : Side := tl (tl (tl (L n)))

theorem L_as_K (n : ℕ) : L n = cons false (K n) := by
  rw [K, ← L_head n, cons_tl]

theorem L_as_J (n : ℕ) : L n = cons false (cons false (cons false (J n))) := by
  funext i
  match i with
  | 0 => exact L_head n
  | 1 => cases n with
    | zero => rw [L_zero]; rfl
    | succ n => rw [L]; rfl
  | 2 => cases n with
    | zero => rw [L_zero]; rfl
    | succ n => rw [L]; rfl
  | i + 3 => rfl

/-- `Lk k v l`: a `k`-bit word `v` (bits `b000`) in front of the side `l`. -/
def Lk : ℕ → ℕ → Side → Side
  | 0, _, l => l
  | k + 1, v, l => cons false (cons false (cons false (cons (v % 2 == 1) (Lk k (v / 2) l))))

/-! ### `b m`: distance from `m` to the next number that is all ones in binary -/

def bb (m : ℕ) : ℕ := 2 ^ (m.log2 + 1) - 1 - m

theorem bb_char (m k : ℕ) (h1 : 2 ^ k ≤ m) (h2 : m < 2 ^ (k + 1)) : bb m = 2 ^ (k + 1) - 1 - m := by
  have hm : m ≠ 0 := by have := @Nat.one_le_two_pow k; omega
  unfold bb; rw [(Nat.log2_eq_iff hm).2 ⟨h1, h2⟩]

theorem bb_one : bb 1 = 0 := by rw [bb_char 1 0 (by decide) (by decide)] <;> decide

theorem log2_spec (m : ℕ) (hm : 0 < m) : 2 ^ m.log2 ≤ m ∧ m < 2 ^ (m.log2 + 1) :=
  ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

theorem bb_spec (m : ℕ) (hm : 0 < m) : ∃ k, 2 ^ k ≤ m ∧ m < 2 ^ (k + 1) ∧ bb m = 2 ^ (k + 1) - 1 - m :=
  ⟨m.log2, (log2_spec m hm).1, (log2_spec m hm).2, rfl⟩

theorem pow_succ2 (k : ℕ) : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega

theorem b_succ (m : ℕ) (hm : 0 < m) (h : 0 < bb m) : bb (m + 1) = bb m - 1 := by
  obtain ⟨k, h1, h2, h3⟩ := bb_spec m hm
  rw [bb_char (m + 1) k (by omega) (by omega)]; omega

theorem b_add (m u : ℕ) (hm : 0 < m) (h : u ≤ bb m) : bb (u + m) = bb m - u := by
  obtain ⟨k, h1, h2, h3⟩ := bb_spec m hm
  rw [bb_char (u + m) k (by omega) (by omega)]; omega

theorem b_add_self (m : ℕ) (hm : 0 < m) : bb (bb m + m) = 0 := by
  rw [b_add m (bb m) hm (Nat.le_refl _)]; omega

theorem b0_succ (m : ℕ) (hm : 0 < m) (h : bb m = 0) : bb (m + 1) = m := by
  obtain ⟨k, h1, h2, h3⟩ := bb_spec m hm
  have e : m + 1 = 2 ^ (k + 1) := by omega
  have p := pow_succ2 (k + 1)
  rw [bb_char (m + 1) (k + 1) (by omega) (by omega)]; omega

theorem bb_le (m : ℕ) (hm : 0 < m) : bb m < m := by
  obtain ⟨k, h1, h2, h3⟩ := bb_spec m hm
  have := pow_succ2 k; omega

theorem bb_double (m : ℕ) (hm : 0 < m) : bb (2 * m) = 2 * bb m + 1 := by
  obtain ⟨k, h1, h2, h3⟩ := bb_spec m hm
  have := pow_succ2 k; have := pow_succ2 (k + 1)
  rw [bb_char (2 * m) (k + 1) (by omega) (by omega)]; omega

theorem bb_double1 (m : ℕ) (hm : 0 < m) : bb (2 * m + 1) = 2 * bb m := by
  obtain ⟨k, h1, h2, h3⟩ := bb_spec m hm
  have := pow_succ2 k; have := pow_succ2 (k + 1)
  rw [bb_char (2 * m + 1) (k + 1) (by omega) (by omega)]; omega

theorem bb_pow4 (k m : ℕ) (hm : 0 < m) : bb (4 ^ k * m) + 1 = 4 ^ k * (bb m + 1) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [show 4 ^ (k + 1) * m = 4 ^ k * (4 * m) by rw [Nat.pow_succ]; rw [Nat.mul_assoc, Nat.mul_comm 4 m]]
    rw [ih (4 * m) (by omega)]
    rw [show 4 * m = 2 * (2 * m) by omega, bb_double _ (by omega), bb_double _ hm, Nat.pow_succ]
    rw [Nat.mul_assoc]; congr 1; omega

end SK
namespace SK
open FCP.BusyBeaver

/-! ## Machine-independent tape lemmas -/

/-- `l <{{q}} r`: head on the innermost cell of `l`. -/
def lc (q : Fin 5) (l r : Side) : SC := ⟨q, tl l, l 0, r⟩
/-- `l {{q}}> r`: head on the innermost cell of `r`. -/
def rc (q : Fin 5) (l r : Side) : SC := ⟨q, l, r 0, tl r⟩

theorem R_4p3 (t : ℕ) : R (4 * t + 3) = cons true (cons true (cons true (cons true (R t)))) := by
  rw [show 4 * t + 3 = 2 * (2 * t + 1) + 1 by omega, R_odd, R_odd]

theorem R_4p2 (t : ℕ) : R (4 * t + 2) = cons true (cons false (cons true (cons true (R t)))) := by
  rw [show 4 * t + 2 = 2 * (2 * t + 1) by omega, R_even _ (by omega), R_odd]

theorem R_4p0 (t : ℕ) (ht : 0 < t) : R (4 * t) = cons true (cons false (cons true (cons false (R t)))) := by
  rw [show 4 * t = 2 * (2 * t) by omega, R_even _ (by omega), R_even _ ht]

theorem Lk_even (k w : ℕ) (l : Side) :
    Lk (k + 1) (2 * w) l = cons false (cons false (cons false (cons false (Lk k w l)))) := by
  show cons false (cons false (cons false (cons ((2 * w) % 2 == 1) (Lk k (2 * w / 2) l)))) = _
  rw [show (2 * w) % 2 = 0 by omega, show 2 * w / 2 = w by omega]; rfl

theorem Lk_odd (k w : ℕ) (l : Side) :
    Lk (k + 1) (2 * w + 1) l = cons false (cons false (cons false (cons true (Lk k w l)))) := by
  show cons false (cons false (cons false (cons ((2 * w + 1) % 2 == 1) (Lk k ((2 * w + 1) / 2) l)))) = _
  rw [show (2 * w + 1) % 2 = 1 by omega, show (2 * w + 1) / 2 = w by omega]; rfl

theorem L_pow (k x : ℕ) (hx : 0 < x) : L (2 ^ k * x) = Lk k 0 (L x) := by
  induction k with
  | zero => simp [Lk]
  | succ k ih =>
    rw [show 2 ^ (k + 1) * x = 2 * (2 ^ k * x) by rw [Nat.pow_succ]; rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc],
      L_even _ (Nat.mul_pos (Nat.two_pow_pos k) hx), ih]
    rfl

theorem tl_Lk (k : ℕ) (X : Side) : tl (Lk k 0 (cons false X)) = Lk k 0 X := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | i + 3 =>
      show Lk (k + 1) 0 (cons false X) (i + 4) = Lk (k + 1) 0 X (i + 3)
      cases i with
      | zero => show Lk k 0 (cons false X) 0 = false; cases k <;> rfl
      | succ i => show Lk k 0 (cons false X) (i + 1) = Lk k 0 X i; rw [← ih]; rfl

theorem tl3_Lk (k : ℕ) (X : Side) :
    tl (tl (tl (Lk k 0 (cons false (cons false (cons false X)))))) = Lk k 0 X := by
  rw [tl_Lk, tl_Lk, tl_Lk]

theorem split_two : ∀ n : ℕ, 0 < n → ∃ k n', n = 2 ^ k * (2 * n' + 1) := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih hn
  obtain ⟨h, rfl | rfl⟩ : ∃ h, n = 2 * h ∨ n = 2 * h + 1 := ⟨n / 2, by omega⟩
  · obtain ⟨k, n', e⟩ := ih h (by omega) (by omega)
    exact ⟨k + 1, n', by rw [e, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]⟩
  · exact ⟨0, h, by rw [Nat.pow_zero, Nat.one_mul]⟩

theorem prepare_K (n : ℕ) (hn : 0 < n) : ∃ k n', n = 2 ^ k * (2 * n' + 1) ∧
    K n = Lk k 0 (cons false (cons false (cons true (cons false (K n'))))) := by
  obtain ⟨k, n', e⟩ := split_two n hn
  refine ⟨k, n', e, ?_⟩
  unfold K
  rw [e, L_pow k _ (by omega), L_odd, L_as_K n', tl_Lk]; rfl

theorem prepare_J (n k n' : ℕ) (e : n = 2 ^ k * (2 * n' + 1)) :
    J n = Lk k 0 (cons true (cons false (cons false (cons false (J n'))))) := by
  unfold J
  rw [e, L_pow k _ (by omega), L_odd, L_as_J n', tl3_Lk]; rfl

theorem J_double (x : ℕ) (hx : 0 < x) : J (2 * x) = cons false (L x) := by
  unfold J; rw [L_even x hx]; rfl

end SK
namespace SK
open FCP.BusyBeaver

/-! ## Skelet #33 -/

abbrev sk33 : TM 5 := BB5.skelet33

theorem L_inc33 : ∀ n r, Reach sk33 (lc 2 (L n) r) (rc 1 (L (n + 1)) r) := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih r
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [show 2 * 0 = 0 from rfl, L_zero, show (0 + 1 : ℕ) = 2 * 0 + 1 from rfl, L_odd, L_zero]
      unfold lc rc
      repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
    · rw [L_even k hk, L_odd k]
      unfold lc rc
      repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
  · rw [L_odd k, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, L_even (k + 1) (by omega)]
    unfold lc rc
    repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
    refine Reach.trans (ih k (by omega) _) ?_
    unfold rc
    repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

theorem R_inc_has0_33 : ∀ m l, 0 < m → 0 < bb m →
    Reach sk33 (rc 4 (cons true l) (R m)) (lc 0 l (cons false (R (m + 1)))) := by
  intro m
  refine Nat.strongRecOn m ?_
  intro m ih l hm hb
  obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
  · rw [R_even k (by omega), R_odd k]
    unfold lc rc
    repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
  · have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · exact absurd hb (by rw [show 2 * 0 + 1 = 1 from rfl, bb_one]; decide)
      · exact h
    have hbk : 0 < bb k := by rw [bb_double1 k hk] at hb; omega
    rw [R_odd k, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, R_even (k + 1) (by omega)]
    unfold rc
    repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
    refine Reach.trans (ih k (by omega) _ hk hbk) ?_
    unfold lc
    repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

/-- `D(n, m) = L(n) <C 1 0 1 0 1 0 R(m)`. -/
def D33 (n m : ℕ) : SC :=
  lc 2 (L n) (cons true (cons false (cons true (cons false (cons true (cons false (R m)))))))

theorem D_inc33 (n m : ℕ) (hm : 0 < m) (hb : 0 < bb m) : Reach sk33 (D33 n m) (D33 (n + 1) (m + 1)) := by
  unfold D33
  refine Reach.trans (L_inc33 n _) ?_
  unfold rc
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
  refine Reach.trans (R_inc_has0_33 m _ hm hb) ?_
  unfold lc
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

theorem D_run33 : ∀ (u n m : ℕ), 0 < m → u ≤ bb m → Reach sk33 (D33 n m) (D33 (u + n) (u + m)) := by
  intro u
  induction u with
  | zero => intro n m _ _; simpa using Reach.refl sk33 (D33 n m)
  | succ u ih =>
    intro n m hm hu
    refine Reach.trans (D_inc33 n m hm (by omega)) ?_
    have := ih (n + 1) (m + 1) (by omega) (by rw [b_succ m hm (by omega)]; omega)
    rw [show u + (n + 1) = u + 1 + n by omega, show u + (m + 1) = u + 1 + m by omega] at this
    exact this

theorem D_finish33 (n m : ℕ) (hm : 0 < m) : Reach sk33 (D33 n m) (D33 (bb m + n) (bb m + m)) :=
  D_run33 (bb m) n m hm (Nat.le_refl _)

theorem R_inc_all1_33 : ∀ m l, 0 < m → bb m = 0 →
    Reach sk33 (rc 4 (cons true l) (R m)) (lc 2 l (R (m + 1))) := by
  intro m
  refine Nat.strongRecOn m ?_
  intro m ih l hm hb
  obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
  · rw [bb_double k (by omega)] at hb; omega
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · have e2 : R (0 + 1 + 1) = cons true (cons false (R 1)) := R_even 1 (by omega)
      have e1 : R 1 = cons true (cons true (R 0)) := R_odd 0
      rw [show 2 * 0 + 1 = 1 from rfl, show (1 + 1 : ℕ) = 0 + 1 + 1 from rfl, e2, e1, R_zero]
      unfold lc rc
      repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
    · have hbk : bb k = 0 := by rw [bb_double1 k hk] at hb; omega
      rw [R_odd k, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, R_even (k + 1) (by omega)]
      unfold rc
      repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
      refine Reach.trans (ih k (by omega) _ hk hbk) ?_
      unfold lc
      repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

/-- `E(n, m) = K(n) <C 1 0 1 0 R(m)`. -/
def E33 (n m : ℕ) : SC := lc 2 (K n) (cons true (cons false (cons true (cons false (R m)))))

theorem start_reset33 (n m : ℕ) (hm : 0 < m) (hb : bb m = 0) :
    Reach sk33 (D33 n m) (E33 (n + 1) (2 * (m + 1) + 1)) := by
  unfold D33 E33
  rw [R_odd (m + 1)]
  refine Reach.trans (L_inc33 n _) ?_
  rw [L_as_K (n + 1)]
  unfold rc
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
  refine Reach.trans (R_inc_all1_33 m _ hm hb) ?_
  unfold lc
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

theorem eat_LI33 (l : Side) (t : ℕ) :
    Reach sk33 (lc 2 (cons false (cons false (cons false (cons true l)))) (R t)) (lc 2 l (R (4 * t + 3))) := by
  rw [R_4p3]
  unfold lc
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

theorem eat_KI33 (l : Side) (t : ℕ) (ht : 0 < t) (hb : 0 < bb t) (hb1 : 0 < bb (t + 1)) :
    Reach sk33 (lc 2 (cons false (cons false (cons true (cons false l)))) (R t))
      (lc 2 l (R (4 * (t + 2)))) := by
  -- case split on the parity of `t`, following the Lean port in mfornet/busybeaver
  rw [R_4p0 _ (by omega)]
  obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
  · have hs : 0 < s := by omega
    have hbs : 0 < bb s := by rw [bb_double1 s hs] at hb1; omega
    rw [R_even s hs, show 2 * s + 2 = 2 * (s + 1) by omega, R_even (s + 1) (by omega)]
    unfold lc
    repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
    refine Reach.trans (R_inc_has0_33 s _ hs hbs) ?_
    unfold lc
    repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
  · have e2 : R (2 * s + 1 + 2) = R (2 * (s + 1) + 1) := by congr 1
    rw [e2, R_odd (s + 1)]
    unfold lc
    repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
    refine Reach.trans (R_inc_has0_33 _ _ ht hb) ?_
    rw [show 2 * s + 1 + 1 = 2 * (s + 1) by omega, R_even (s + 1) (by omega)]
    unfold lc
    repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

theorem Lk_inc33 : ∀ (k v : ℕ) (l r : Side), v + 1 < 2 ^ k →
    Reach sk33 (lc 2 (Lk k v l) r) (rc 1 (Lk k (v + 1) l) r) := by
  intro k
  induction k with
  | zero => intro v l r h; rw [Nat.pow_zero] at h; omega
  | succ k ih =>
    intro v l r h
    have p := pow_succ2 k
    obtain ⟨w, rfl | rfl⟩ : ∃ w, v = 2 * w ∨ v = 2 * w + 1 := ⟨v / 2, by omega⟩
    · rw [Lk_even, Lk_odd]
      unfold lc rc
      repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
    · rw [Lk_odd, show 2 * w + 1 + 1 = 2 * (w + 1) by omega, Lk_even]
      unfold lc
      repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
      refine Reach.trans (ih w l _ (by omega)) ?_
      unfold rc
      repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

/-- `Lk(v) <C 1 0 1 0 R(m)`. -/
def LaR33 (k v : ℕ) (l : Side) (m : ℕ) : SC :=
  lc 2 (Lk k v l) (cons true (cons false (cons true (cons false (R m)))))

theorem LaR_inc33 (k v : ℕ) (l : Side) (m : ℕ) (hm : 0 < m) (hb : 0 < bb m) (hb1 : 0 < bb (m + 1))
    (hv : v + 1 < 2 ^ k) : Reach sk33 (LaR33 k v l m) (LaR33 k (v + 1) l (m + 2)) := by
  unfold LaR33
  refine Reach.trans (Lk_inc33 k v l _ hv) ?_
  unfold rc
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
  refine Reach.trans (R_inc_has0_33 m _ hm hb) ?_
  unfold lc
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)
  refine Reach.trans (R_inc_has0_33 (m + 1) _ (by omega) hb1) ?_
  unfold lc
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

theorem LaR_incs33 : ∀ (u k v : ℕ) (l : Side) (m : ℕ), 0 < m → 2 * u ≤ bb m → v + u < 2 ^ k →
    Reach sk33 (LaR33 k v l m) (LaR33 k (v + u) l (2 * u + m)) := by
  intro u
  induction u with
  | zero => intro k v l m _ _ _; simpa using Reach.refl sk33 (LaR33 k v l m)
  | succ u ih =>
    intro k v l m hm hu hv
    have h1 : bb (m + 1) = bb m - 1 := b_succ m hm (by omega)
    have h2 : bb (m + 1 + 1) = bb (m + 1) - 1 := b_succ (m + 1) (by omega) (by omega)
    refine Reach.trans (LaR_inc33 k v l m hm (by omega) (by omega) (by omega)) ?_
    have := ih k (v + 1) l (m + 2) (by omega) (by rw [show m + 2 = m + 1 + 1 by omega, h2, h1]; omega)
      (by omega)
    rw [show v + 1 + u = v + (u + 1) by omega, show 2 * u + (m + 2) = 2 * (u + 1) + m by omega] at this
    exact this

theorem LaR_max33 (k : ℕ) (l : Side) (m : ℕ) (hm : 0 < m) (h : 2 * (2 ^ k - 1) ≤ bb m) :
    Reach sk33 (LaR33 k 0 l m) (LaR33 k (2 ^ k - 1) l (2 * (2 ^ k - 1) + m)) := by
  have := LaR_incs33 (2 ^ k - 1) k 0 l m hm h (by have := @Nat.one_le_two_pow k; omega)
  rwa [Nat.zero_add] at this

theorem eat_bin_max33 : ∀ (k : ℕ) (l : Side) (t : ℕ), 0 < t → 0 < bb t → 0 < bb (t + 1) →
    Reach sk33 (lc 2 (Lk k (2 ^ k - 1) (cons false (cons false (cons true (cons false l))))) (R t))
      (lc 2 l (cons true (cons false (cons true (cons false (R (4 ^ k * (t + 1) + 1))))))) := by
  intro k
  induction k with
  | zero =>
    intro l t ht hb hb1
    have := eat_KI33 l t ht hb hb1
    rw [R_4p0 _ (by omega)] at this
    show Reach sk33 (lc 2 (cons false (cons false (cons true (cons false l)))) (R t)) _
    rw [Nat.pow_zero, Nat.one_mul]; exact this
  | succ k ih =>
    intro l t ht hb hb1
    have p := pow_succ2 k
    have q := @Nat.one_le_two_pow k
    rw [show 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 by omega, Lk_odd]
    refine Reach.trans (eat_LI33 _ t) ?_
    have hb' : 0 < bb (4 * t + 3) := by
      rw [show 4 * t + 3 = 2 * (2 * t + 1) + 1 by omega, bb_double1 _ (by omega), bb_double1 _ ht]; omega
    have hb1' : 0 < bb (4 * t + 3 + 1) := by
      rw [show 4 * t + 3 + 1 = 2 * (2 * (t + 1)) by omega, bb_double _ (by omega)]; omega
    have := ih l (4 * t + 3) (by omega) hb' hb1'
    rw [show 4 ^ k * (4 * t + 3 + 1) = 4 ^ (k + 1) * (t + 1) by
      rw [Nat.pow_succ, Nat.mul_assoc, show 4 * t + 3 + 1 = 4 * (t + 1) by omega]] at this
    exact this

/-- `f m k` from the Coq proof. -/
def f33 (m k : ℕ) : ℕ := 2 * (2 * (2 ^ k - 1) + m)

theorem drop_KI33 (k : ℕ) (l : Side) (m : ℕ) (hm : 0 < m) (h : 2 * (2 ^ k - 1) ≤ bb m) :
    Reach sk33 (LaR33 k 0 (cons false (cons false (cons true (cons false l)))) m)
      (lc 2 l (cons true (cons false (cons true (cons false (R (4 ^ k * (2 * f33 m k + 1) + 1))))))) := by
  refine Reach.trans (LaR_max33 k _ m hm h) ?_
  unfold LaR33
  have hy : 0 < 2 * (2 ^ k - 1) + m := by omega
  rw [← R_4p0 _ hy]
  have := eat_bin_max33 k l (4 * (2 * (2 ^ k - 1) + m)) (by omega)
    (by rw [show 4 * (2 * (2 ^ k - 1) + m) = 2 * (2 * (2 * (2 ^ k - 1) + m)) by omega,
          bb_double _ (by omega)]; omega)
    (by rw [show 4 * (2 * (2 ^ k - 1) + m) + 1 = 2 * (2 * (2 * (2 ^ k - 1) + m)) + 1 by omega,
          bb_double1 _ (by omega), bb_double _ (by omega)]; omega)
  rw [show 4 * (2 * (2 ^ k - 1) + m) + 1 = 2 * f33 m k + 1 by unfold f33; omega] at this
  exact this

/-! ### The `leads` invariant: `n = 1` or `n` starts with `11` in binary -/

def Leads (n : ℕ) : Prop := n = 1 ∨ ∃ q r, n = 3 * 2 ^ q + r ∧ r < 2 ^ q

theorem leads_even_rev (x : ℕ) (h : Leads (2 * x)) : Leads x := by
  rcases h with h | ⟨q, r, e, hr⟩
  · omega
  · right
    rcases q with _ | q
    · simp at e hr; omega
    · have p := pow_succ2 q
      exact ⟨q, r / 2, by omega, by omega⟩

theorem leads_odd_rev (x : ℕ) (hx : 0 < x) (h : Leads (2 * x + 1)) : Leads x := by
  rcases h with h | ⟨q, r, e, hr⟩
  · omega
  · rcases q with _ | q
    · left; simp at e hr; omega
    · right
      have p := pow_succ2 q
      exact ⟨q, r / 2, by omega, by omega⟩

theorem leads_pow_rev : ∀ (k x : ℕ), Leads (2 ^ k * x) → Leads x := by
  intro k
  induction k with
  | zero => intro x h; simpa using h
  | succ k ih =>
    intro x h
    apply ih
    apply leads_even_rev
    rw [show 2 * (2 ^ k * x) = 2 ^ (k + 1) * x by rw [pow_succ]; ring]; exact h

theorem leads_pow2 (k : ℕ) (h : Leads (2 ^ k)) : k = 0 := by
  rcases h with h | ⟨q, r, e, hr⟩
  · exact (Nat.pow_eq_one.1 h).resolve_left (by norm_num)
  · exfalso
    have h1 : 2 ^ (q + 1) < 2 ^ k := by rw [pow_succ]; omega
    have h2 : 2 ^ k < 2 ^ (q + 2) := by rw [pow_succ, pow_succ]; omega
    rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h1 h2
    omega

/-- Arithmetic core of the reset step, taken from the Lean port in mfornet/busybeaver
(`Skelet33.reset_arith`). -/
theorem reset_arith {q r k p : ℕ} (hrlt : r < 2 ^ q) (h2n : 2 * (2 ^ k + 2 ^ (k + 1) * p) ≤ r) :
    ∃ (q' r' : ℕ),
      2 ^ (2 * k) * (4 * ((3 * 2 ^ q + r) - 2 * (2 ^ k - 1)) + 3) - 2 = 3 * 2 ^ q' + r'
        ∧ 2 * p ≤ r' ∧ r' < 2 ^ q' := by
  refine' ⟨ q + 2 * k + 2, _, _, _, _ ⟩;
  exact 2 ^ ( 2 * k ) * ( 4 * r - 8 * 2 ^ k + 11 ) - 2;
  · have hc : (1:ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    have hr2c : 2 * 2 ^ k ≤ r := by
      have : 2 * 2 ^ k ≤ 2 * (2 ^ k + 2 ^ (k + 1) * p) := by
        nlinarith [Nat.zero_le (2 ^ (k + 1) * p)]
      omega
    have hpowq : 2 ^ (q + 2 * k + 2) = 4 * (2 ^ (2 * k) * 2 ^ q) := by
      rw [pow_add, pow_add]; ring
    set a := 2 ^ (2 * k) with ha
    set b := 2 ^ q with hb
    have ha1 : 1 ≤ a := Nat.one_le_two_pow
    set s := 4 * r - 8 * 2 ^ k + 11 with hs
    have key : 4 * (3 * b + r - 2 * (2 ^ k - 1)) + 3 = 12 * b + s := by rw [hs]; omega
    have hexp : a * (12 * b + s) = 12 * (a * b) + a * s := by ring
    have hY : 2 ≤ a * s := by
      have hs11 : 11 ≤ s := by omega
      nlinarith
    rw [hpowq, key, hexp]
    omega
  · refine' le_tsub_of_add_le_left _;
    ring_nf at *;
    nlinarith [ pow_pos ( by decide : 0 < 2 ) k, pow_pos ( by decide : 0 < 2 ) ( k * 2 ), Nat.sub_add_cancel ( show 2 ^ k * 8 ≤ r * 4 from by nlinarith [ pow_pos ( by decide : 0 < 2 ) k ] ) ];
  · rw [ tsub_lt_iff_left ];
    · norm_num [ pow_add ] at *;
      nlinarith [ pow_pos ( by decide : 0 < 2 ) k, pow_pos ( by decide : 0 < 2 ) ( 2 * k ), Nat.sub_add_cancel ( show 8 * 2 ^ k ≤ 4 * r from by nlinarith [ pow_pos ( by decide : 0 < 2 ) k ] ) ];
    · exact le_trans ( by norm_num ) ( Nat.mul_le_mul ( Nat.one_le_pow _ _ ( by norm_num ) ) ( Nat.le_add_left _ _ ) )

def RI33 (n m : ℕ) : Prop := Leads n ∧ ∃ q r, bb m = 3 * 2 ^ q + r ∧ 2 * n ≤ r ∧ r < 2 ^ q

theorem RI33_leads (n m : ℕ) (h : RI33 n m) : Leads (bb m) := by
  obtain ⟨_, q, r, e, _, hr⟩ := h
  exact Or.inr ⟨q, r, e, hr⟩

theorem K_one : K 1 = cons false (cons false (cons true zeros)) := by
  unfold K
  rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, L_odd, L_zero]; rfl

theorem step_reset_odd33 (n m : ℕ) : Reach sk33 (E33 (2 * n + 1) m) (E33 n (4 * m + 2)) := by
  unfold E33
  rw [R_4p2, show K (2 * n + 1) = cons false (cons false (cons true (cons false (K n)))) by
    unfold K; rw [L_odd, L_as_K n]; rfl]
  unfold lc
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

theorem step_reset33 (n m : ℕ) (hn1 : n ≠ 1) (hn : 0 < n) (hm : 0 < m) (hinv : RI33 n m) :
    ∃ n' m', Reach sk33 (E33 n m) (E33 n' m') ∧ n' < n ∧ 0 < n' ∧ RI33 n' m' ∧ 0 < m' := by
  obtain ⟨hlead, q, r, hbm, h2n, hrq⟩ := hinv
  obtain ⟨k, n', e, hK⟩ := prepare_K n hn
  rcases Nat.eq_zero_or_pos n' with rfl | hn'
  · rw [e, show 2 * 0 + 1 = 1 from rfl, Nat.mul_one] at hlead hn1
    have := leads_pow2 k hlead
    subst this; simp at hn1
  have q1 := @Nat.one_le_two_pow k
  have q4 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by omega)
  have eP : 2 ^ k * (2 * n' + 1) = 2 * (2 ^ k * n') + 2 ^ k := by ring
  have hPn : n' ≤ 2 ^ k * n' := Nat.le_mul_of_pos_left n' (by omega)
  have hkb : 2 * (2 ^ k - 1) ≤ bb m := by omega
  -- the new right counter and its `b`
  have hy : bb (2 * (2 ^ k - 1) + m) = bb m - 2 * (2 ^ k - 1) := b_add m _ hm hkb
  have hX : bb (2 * f33 m k + 1) = 4 * bb (2 * (2 ^ k - 1) + m) + 2 := by
    unfold f33; rw [bb_double1 _ (by omega), bb_double _ (by omega)]; ring
  have hpow := bb_pow4 k (2 * f33 m k + 1) (by omega)
  have hpos : 0 < bb (4 ^ k * (2 * f33 m k + 1)) := by rw [hX] at hpow; nlinarith
  have hbm' : bb (4 ^ k * (2 * f33 m k + 1) + 1) = bb (4 ^ k * (2 * f33 m k + 1)) - 1 :=
    b_succ _ (by unfold f33; positivity) hpos
  refine ⟨n', 4 ^ k * (2 * f33 m k + 1) + 1, ?_, by omega, hn', ⟨?_, ?_⟩, by omega⟩
  · unfold E33
    rw [hK]
    exact drop_KI33 k (K n') m hm hkb
  · apply leads_odd_rev n' hn'
    exact leads_pow_rev k _ (e ▸ hlead)
  · obtain ⟨q', r', h1, h2, h3⟩ := reset_arith (q := q) (r := r) (k := k) (p := n') hrq
      (by rw [show 2 ^ k + 2 ^ (k + 1) * n' = 2 ^ k * (2 * n' + 1) by ring, ← e]; omega)
    refine ⟨q', r', ?_, h2, h3⟩
    have A : bb (4 ^ k * (2 * f33 m k + 1)) + 1
        = 4 ^ k * (4 * ((3 * 2 ^ q + r) - 2 * (2 ^ k - 1)) + 3) := by
      rw [hpow, hX, hy, hbm]
    rw [show 2 ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num] at h1
    rw [hbm', ← h1]
    omega

theorem do_reset33 : ∀ n m, 0 < n → 0 < m → RI33 n m →
    ∃ m', Reach sk33 (E33 n m) (E33 1 m') ∧ Leads (bb m') ∧ 0 < m' := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih m hn hm hinv
  by_cases hn1 : n = 1
  · subst hn1; exact ⟨m, Reach.refl _ _, RI33_leads 1 m hinv, hm⟩
  · obtain ⟨n', m', hr, hlt, hn', hinv', hm'⟩ := step_reset33 n m hn1 hn hm hinv
    obtain ⟨m'', hr', hl, hm''⟩ := ih n' hlt m' hn' hm' hinv'
    exact ⟨m'', hr.trans hr', hl, hm''⟩

theorem E_start33 (m : ℕ) : Prog sk33 (E33 1 m) (D33 0 (2 * m + 1)) := by
  unfold E33 D33
  rw [K_one, L_zero, R_odd m]
  unfold lc
  refine Prog.step rfl ?_
  repeat (first | exact Reach.refl _ _ | refine Reach.step rfl ?_)

theorem bb_16 (x : ℕ) (hx : 0 < x) : bb (16 * x + 6) = 16 * bb x + 9 := by
  rw [show 16 * x + 6 = 2 * (2 * (2 * (2 * x) + 1) + 1) by ring, bb_double _ (by omega),
    bb_double1 _ (by omega), bb_double1 _ (by omega), bb_double _ hx]; ring

theorem E_next33 (m : ℕ) (hm : 0 < m) (hl : Leads (bb m)) :
    ∃ m', Prog sk33 (E33 1 m) (E33 1 m') ∧ Leads (bb m') ∧ 0 < m' := by
  have hbm : 0 < bb m := by rcases hl with h | ⟨q, r, e, _⟩ <;> [omega; (have := @Nat.one_le_two_pow q; omega)]
  set bm := bb m with hbm_def
  have h21 : bb (2 * m + 1) = 2 * bm := bb_double1 m hm
  have hs := b_add_self (2 * m + 1) (by omega)
  rw [h21] at hs
  obtain ⟨j, hj1, hj2, hj3⟩ := bb_spec m hm
  have pj := pow_succ2 j
  have hsv : bm + m + 1 = 2 ^ (j + 1) := by omega
  have hbs : bb (2 ^ (j + 1)) = 2 ^ (j + 1) - 1 := by
    rw [bb_char (2 ^ (j + 1)) (j + 1) le_rfl (by rw [pow_succ]; omega)]; omega
  have hinv : RI33 bm (16 * (bm + m + 1) + 6) := by
    refine ⟨hl, j + 3, 2 ^ (j + 3) - 7, ?_, ?_, ?_⟩
    · rw [bb_16 _ (by omega), hsv, hbs]
      have : 2 ^ (j + 3) = 4 * 2 ^ (j + 1) := by rw [pow_add, pow_add]; ring
      omega
    · have : 2 ^ (j + 3) = 8 * 2 ^ j := by rw [pow_add]; ring
      omega
    · have : 8 ≤ 2 ^ (j + 3) := by rw [pow_add]; have := @Nat.one_le_two_pow j; omega
      omega
  obtain ⟨m', hr, hl', hm'⟩ := do_reset33 bm _ hbm (by omega) hinv
  refine ⟨m', ?_, hl', hm'⟩
  have p1 := D_finish33 0 (2 * m + 1) (by omega)
  rw [h21, Nat.add_zero] at p1
  have p2 := start_reset33 (2 * bm) (2 * bm + (2 * m + 1)) (by omega) hs
  have p3 := step_reset_odd33 bm (2 * (2 * bm + (2 * m + 1) + 1) + 1)
  rw [show 4 * (2 * (2 * bm + (2 * m + 1) + 1) + 1) + 2 = 16 * (bm + m + 1) + 6 by ring] at p3
  exact (((E_start33 m).trans_reach p1).trans_reach p2).trans_reach (p3.trans hr)

theorem start33a : Reach sk33 ⟨0, zeros, false, zeros⟩
    ⟨2, cons false (cons true (cons true (cons false (cons false (cons true (zeros)))))), false, cons true (cons false (cons true (cons true (zeros))))⟩ := by
  iterate 60 refine Reach.step rfl ?_
  exact Reach.refl _ _

theorem start33b : Reach sk33
    ⟨2, cons false (cons true (cons true (cons false (cons false (cons true (zeros)))))), false, cons true (cons false (cons true (cons true (zeros))))⟩
    ⟨4, cons true (cons true (cons false (cons false (cons false (cons false (cons true (zeros))))))), true, cons true (cons false (cons true (cons true (cons true (cons true (cons true (cons true (zeros))))))))⟩ := by
  iterate 60 refine Reach.step rfl ?_
  exact Reach.refl _ _

theorem start33c : Reach sk33
    ⟨4, cons true (cons true (cons false (cons false (cons false (cons false (cons true (zeros))))))), true, cons true (cons false (cons true (cons true (cons true (cons true (cons true (cons true (zeros))))))))⟩
    (E33 1 17) := by
  have h17 : R 17 = cons true (cons true (R 8)) := R_odd 8
  have h8 : R 8 = cons true (cons false (R 4)) := R_even 4 (by omega)
  have h4 : R 4 = cons true (cons false (R 2)) := R_even 2 (by omega)
  have h2 : R 2 = cons true (cons false (R 1)) := R_even 1 (by omega)
  have h1 : R 1 = cons true (cons true (R 0)) := R_odd 0
  unfold E33 lc
  rw [K_one, h17, h8, h4, h2, h1, R_zero]
  iterate 55 refine Reach.step rfl ?_
  exact Reach.refl _ _

theorem start33 : Reach sk33 ⟨0, zeros, false, zeros⟩ (E33 1 17) :=
  (start33a.trans start33b).trans start33c


theorem sk33_nonhalt : ∀ t, runS sk33 ⟨0, zeros, false, zeros⟩ t ≠ none := by
  have hl : Leads (bb 17) := by
    rw [bb_char 17 4 (by norm_num) (by norm_num)]
    exact Or.inr ⟨2, 2, by norm_num, by norm_num⟩
  refine nonhalt_of_reach start33 ?_
  intro t
  refine nonhalt_cond (ι := ℕ) sk33 (fun m => E33 1 m) (fun m => Leads (bb m) ∧ 0 < m) ?_ t 17
    ⟨hl, by norm_num⟩
  rintro m ⟨hl, hm⟩
  obtain ⟨m', hp, hl', hm'⟩ := E_next33 m hm hl
  exact ⟨m', hp, hl', hm'⟩

end SK

theorem solution :
    ∀ t : ℕ, FCP.BusyBeaver.run BB5.skelet33 (FCP.BusyBeaver.init (by omega)) t ≠ none :=
  SK.nonhalt_of_S BB5.skelet33 _ ⟨0, SK.zeros, false, SK.zeros⟩ SK.rep_init SK.sk33_nonhalt
