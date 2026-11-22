-- Prove2me | solution 2 for BB5.champion_halts
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-22T21:04:34.77638+00:00
-- url     : https://prove2.me/submissions/6c4be3fe-db34-4361-bd7d-651b978d113a

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner

namespace ChampAux
open FCP.BusyBeaver



/-! ### Generic facts about `run` -/

theorem run_trans {n : ℕ} (M : TM n) (c d : Config n) (a : ℕ) (h : run M c a = some d) :
    ∀ b : ℕ, run M c (a + b) = run M d b := by
  intro b
  induction b with
  | zero => exact h
  | succ b ih =>
    show (run M c (a + b)).bind (step M) = (run M d b).bind (step M)
    rw [ih]

theorem run_none {n : ℕ} (M : TM n) (c : Config n) (s : ℕ) (h : run M c s = none) :
    ∀ m : ℕ, run M c (s + m) = none := by
  intro m
  induction m with
  | zero => exact h
  | succ m ih =>
    show (run M c (s + m)).bind (step M) = none
    rw [ih]; rfl

theorem chain {c d e : Config 5} {a b : ℕ} (h1 : run BB5.winner c a = some d)
    (h2 : run BB5.winner d b = some e) : run BB5.winner c (a + b) = some e := by
  rw [run_trans _ c d a h1 b]; exact h2

theorem chain1 {c d e : Config 5} {a : ℕ} (h1 : run BB5.winner c a = some d)
    (h2 : step BB5.winner d = some e) : run BB5.winner c (a + 1) = some e := by
  rw [run_trans _ c d a h1 1]; exact h2

/-! ### Configurations described by a predicate on the tape -/

/-- `Is c q h P`: state `q`, head at `h`, and the cells holding `1` are exactly those satisfying `P`. -/
def Is (c : Config 5) (q : Fin 5) (h : ℤ) (P : ℤ → Prop) : Prop :=
  c.state = q ∧ c.head = h ∧ ∀ i : ℤ, c.tape i = true ↔ P i

theorem Is.congr {c : Config 5} {q : Fin 5} {h : ℤ} {P Q : ℤ → Prop} (hc : Is c q h P)
    (hPQ : ∀ i, P i ↔ Q i) : Is c q h Q :=
  ⟨hc.1, hc.2.1, fun i => (hc.2.2 i).trans (hPQ i)⟩

theorem Is.read1 {c : Config 5} {q : Fin 5} {h : ℤ} {P : ℤ → Prop} (hc : Is c q h P) (hp : P h) :
    c.tape h = true := (hc.2.2 h).2 hp

theorem Is.read0 {c : Config 5} {q : Fin 5} {h : ℤ} {P : ℤ → Prop} (hc : Is c q h P) (hp : ¬ P h) :
    c.tape h = false := by
  cases hv : c.tape h
  · rfl
  · exact absurd ((hc.2.2 h).1 hv) hp

theorem step_some_of {c : Config 5} {q : Fin 5} {h : ℤ} {P : ℤ → Prop} {b w d : Bool} {q' : Fin 5}
    (hc : Is c q h P) (hb : c.tape h = b) (ht : BB5.winner.trans q b = (w, d, some q')) :
    step BB5.winner c = some ⟨q', if d then c.head + 1 else c.head - 1, Function.update c.tape c.head w⟩ := by
  have hb' : c.tape c.head = b := by rw [hc.2.1]; exact hb
  unfold step; rw [hb', hc.1, ht]

theorem sR1 {c : Config 5} {q : Fin 5} {h : ℤ} {P : ℤ → Prop} {b : Bool} {q' : Fin 5}
    (Q : ℤ → Prop) (hc : Is c q h P) (hb : c.tape h = b)
    (ht : BB5.winner.trans q b = (true, true, some q')) (hQ : ∀ i, Q i ↔ (i = h ∨ P i)) :
    ∃ c', step BB5.winner c = some c' ∧ Is c' q' (h + 1) Q := by
  refine ⟨_, step_some_of hc hb ht, rfl, by show c.head + 1 = h + 1; rw [hc.2.1], ?_⟩
  intro i
  show Function.update c.tape c.head true i = true ↔ Q i
  rw [hQ i, Function.update_apply, hc.2.1]
  by_cases hi : i = h
  · rw [if_pos hi]; exact ⟨fun _ => Or.inl hi, fun _ => rfl⟩
  · rw [if_neg hi, hc.2.2 i]; exact ⟨Or.inr, fun h' => h'.resolve_left hi⟩

theorem sL1 {c : Config 5} {q : Fin 5} {h : ℤ} {P : ℤ → Prop} {b : Bool} {q' : Fin 5}
    (Q : ℤ → Prop) (hc : Is c q h P) (hb : c.tape h = b)
    (ht : BB5.winner.trans q b = (true, false, some q')) (hQ : ∀ i, Q i ↔ (i = h ∨ P i)) :
    ∃ c', step BB5.winner c = some c' ∧ Is c' q' (h - 1) Q := by
  refine ⟨_, step_some_of hc hb ht, rfl, by show c.head - 1 = h - 1; rw [hc.2.1], ?_⟩
  intro i
  show Function.update c.tape c.head true i = true ↔ Q i
  rw [hQ i, Function.update_apply, hc.2.1]
  by_cases hi : i = h
  · rw [if_pos hi]; exact ⟨fun _ => Or.inl hi, fun _ => rfl⟩
  · rw [if_neg hi, hc.2.2 i]; exact ⟨Or.inr, fun h' => h'.resolve_left hi⟩

theorem sL0 {c : Config 5} {q : Fin 5} {h : ℤ} {P : ℤ → Prop} {b : Bool} {q' : Fin 5}
    (Q : ℤ → Prop) (hc : Is c q h P) (hb : c.tape h = b)
    (ht : BB5.winner.trans q b = (false, false, some q')) (hQ : ∀ i, Q i ↔ (i ≠ h ∧ P i)) :
    ∃ c', step BB5.winner c = some c' ∧ Is c' q' (h - 1) Q := by
  refine ⟨_, step_some_of hc hb ht, rfl, by show c.head - 1 = h - 1; rw [hc.2.1], ?_⟩
  intro i
  show Function.update c.tape c.head false i = true ↔ Q i
  rw [hQ i, Function.update_apply, hc.2.1]
  by_cases hi : i = h
  · rw [if_pos hi]; exact ⟨fun h' => absurd h' (by decide), fun h' => absurd hi h'.1⟩
  · rw [if_neg hi, hc.2.2 i]; exact ⟨fun h' => ⟨hi, h'⟩, fun h' => h'.2⟩

theorem sHalt {c : Config 5} {h : ℤ} {P : ℤ → Prop} (hc : Is c 4 h P) (hp : ¬ P h) :
    step BB5.winner c = none := by
  have hb' : c.tape c.head = false := by rw [hc.2.1]; exact hc.read0 hp
  unfold step; rw [hb', hc.1]; rfl

/-! ### Sweeps over blocks of ones (the tape is unchanged) -/

theorem sweepB : ∀ (m : ℕ) (c : Config 5) (h : ℤ) (P : ℤ → Prop), Is c 1 h P →
    (∀ j : ℕ, j < m → P (h + j)) → ∃ c', run BB5.winner c m = some c' ∧ Is c' 1 (h + m) P := by
  intro m
  induction m with
  | zero => intro c h P hc _; exact ⟨c, rfl, by simpa using hc⟩
  | succ m ih =>
    intro c h P hc hP
    have h0 : P h := by simpa using hP 0 (by omega)
    obtain ⟨c1, e1, hc1⟩ := sR1 P hc (hc.read1 h0) rfl (fun i => ⟨Or.inr, fun hi => hi.elim (· ▸ h0) id⟩)
    obtain ⟨c2, e2, hc2⟩ := ih c1 (h + 1) P hc1 (fun j hj => by
      have := hP (j + 1) (by omega)
      rw [show h + 1 + (j : ℤ) = h + ((j + 1 : ℕ) : ℤ) by omega]; exact this)
    refine ⟨c2, ?_, hc2.1, by rw [hc2.2.1]; omega, hc2.2.2⟩
    rw [Nat.add_comm]; exact chain (show run BB5.winner c 1 = some c1 from e1) e2

theorem sweepD : ∀ (m : ℕ) (c : Config 5) (h : ℤ) (P : ℤ → Prop), Is c 3 h P →
    (∀ j : ℕ, j < m → P (h - j)) → ∃ c', run BB5.winner c m = some c' ∧ Is c' 3 (h - m) P := by
  intro m
  induction m with
  | zero => intro c h P hc _; exact ⟨c, rfl, by simpa using hc⟩
  | succ m ih =>
    intro c h P hc hP
    have h0 : P h := by simpa using hP 0 (by omega)
    obtain ⟨c1, e1, hc1⟩ := sL1 P hc (hc.read1 h0) rfl (fun i => ⟨Or.inr, fun hi => hi.elim (· ▸ h0) id⟩)
    obtain ⟨c2, e2, hc2⟩ := ih c1 (h - 1) P hc1 (fun j hj => by
      have := hP (j + 1) (by omega)
      rw [show h - 1 - (j : ℤ) = h - ((j + 1 : ℕ) : ℤ) by omega]; exact this)
    refine ⟨c2, ?_, hc2.1, by rw [hc2.2.1]; omega, hc2.2.2⟩
    rw [Nat.add_comm]; exact chain (show run BB5.winner c 1 = some c1 from e1) e2

/-! ### The configurations `g` at an arbitrary offset -/

/-- `G o y`: state `A`, head at `o`, ones exactly on `[o+1, o+y]`. -/
def G (o : ℤ) (y : ℕ) : Config 5 := ⟨0, o, fun i => decide (o + 1 ≤ i ∧ i ≤ o + y)⟩

theorem G_is (o : ℤ) (y : ℕ) : Is (G o y) 0 o (fun i => o + 1 ≤ i ∧ i ≤ o + y) :=
  ⟨rfl, rfl, fun _ => decide_eq_true_iff⟩

theorem eq_G {c : Config 5} {o : ℤ} {y : ℕ} {P : ℤ → Prop} (hc : Is c 0 o P)
    (hP : ∀ i, P i ↔ (o + 1 ≤ i ∧ i ≤ o + y)) : c = G o y := by
  obtain ⟨s, hd, tp⟩ := c
  obtain ⟨hs, hh, ht⟩ := hc
  simp only at hs hh ht
  subst hs hh
  have : tp = (G hd y).tape := by
    funext i
    show tp i = decide (hd + 1 ≤ i ∧ i ≤ hd + y)
    cases hv : tp i
    · exact (decide_eq_false (fun h' => absurd ((ht i).2 ((hP i).2 h')) (by rw [hv]; decide))).symm
    · exact (decide_eq_true ((hP i).1 ((ht i).1 hv))).symm
  rw [this]; rfl

/-! ### Phase 1: the opening sweep -/

/-- Pattern during the leftward loop, with head at `p`. -/
def LoopP (o : ℤ) (y : ℕ) (p i : ℤ) : Prop :=
  (o ≤ i ∧ i ≤ p) ∨ (p < i ∧ i ≤ o + y + 2 ∧ (o + y + 2 - i) % 3 = 0) ∨ i = o + y + 3

theorem opening (o : ℤ) (y : ℕ) : ∃ c, run BB5.winner (G o y) (y + 4) = some c ∧
    Is c 0 (o + y + 2) (LoopP o y (o + y + 2)) := by
  have g := G_is o y
  obtain ⟨c1, e1, h1⟩ := sR1 (fun i => i = o ∨ (o + 1 ≤ i ∧ i ≤ o + y)) g (g.read0 (by omega)) rfl
    (fun _ => Iff.rfl)
  obtain ⟨c2, e2, h2⟩ := sweepB y c1 (o + 1) _ h1 (fun j hj => Or.inr (by omega))
  obtain ⟨c3, e3, h3⟩ := sR1 (fun i => i = o + 1 + y ∨ (i = o ∨ (o + 1 ≤ i ∧ i ≤ o + y))) h2
    (h2.read0 (by omega)) rfl (fun _ => Iff.rfl)
  obtain ⟨c4, e4, h4⟩ := sR1 (fun i => i = o + 1 + y + 1 ∨ (i = o + 1 + y ∨ (i = o ∨ (o + 1 ≤ i ∧ i ≤ o + y))))
    h3 (h3.read0 (by omega)) rfl (fun _ => Iff.rfl)
  obtain ⟨c5, e5, h5⟩ := sL1 (fun i => i = o + 1 + y + 1 + 1 ∨
      (i = o + 1 + y + 1 ∨ (i = o + 1 + y ∨ (i = o ∨ (o + 1 ≤ i ∧ i ≤ o + y))))) h4
    (h4.read0 (by omega)) rfl (fun _ => Iff.rfl)
  refine ⟨c5, ?_, ?_⟩
  · rw [show y + 4 = 1 + y + 1 + 1 + 1 by omega]
    exact chain1 (chain1 (chain1 (chain (show run BB5.winner (G o y) 1 = some c1 from e1) e2) e3) e4) e5
  · refine ⟨h5.1, by rw [h5.2.1]; omega, fun i => (h5.2.2 i).trans ?_⟩
    dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega))

/-! ### Phase 2: the leftward loop -/

theorem loop3 (o : ℤ) (y : ℕ) (p : ℤ) (c : Config 5) (hc : Is c 0 p (LoopP o y p))
    (hp : o + 2 ≤ p) (hp' : p ≤ o + y + 2) (hmod : (o + y + 2 - p) % 3 = 0) :
    ∃ c', run BB5.winner c 3 = some c' ∧ Is c' 0 (p - 3) (LoopP o y (p - 3)) := by
  obtain ⟨c1, e1, h1⟩ := sL1 (fun i => i = p ∨ LoopP o y p i) hc
    (hc.read1 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨c2, e2, h2⟩ := sL0 (fun i => i ≠ p - 1 ∧ (i = p ∨ LoopP o y p i)) h1
    (h1.read1 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨c3, e3, h3⟩ := sL0 (fun i => i ≠ p - 1 - 1 ∧ (i ≠ p - 1 ∧ (i = p ∨ LoopP o y p i))) h2
    (h2.read1 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  refine ⟨c3, chain1 (chain1 (show run BB5.winner c 1 = some c1 from e1) e2) e3, h3.1,
    by rw [h3.2.1]; omega, fun i => (h3.2.2 i).trans ?_⟩
  dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega))

theorem loopK (o : ℤ) (y : ℕ) : ∀ (k : ℕ) (c : Config 5), Is c 0 (o + y + 2) (LoopP o y (o + y + 2)) →
    3 * k ≤ y + 3 → ∃ c', run BB5.winner c (3 * k) = some c' ∧
      Is c' 0 (o + y + 2 - 3 * k) (LoopP o y (o + y + 2 - 3 * k)) := by
  intro k
  induction k with
  | zero => intro c hc _; exact ⟨c, rfl, by simpa using hc⟩
  | succ k ih =>
    intro c hc hk
    obtain ⟨c1, e1, h1⟩ := ih c hc (by omega)
    obtain ⟨c2, e2, h2⟩ := loop3 o y _ c1 h1 (by omega) (by omega) (by omega)
    refine ⟨c2, ?_, ?_⟩
    · rw [show 3 * (k + 1) = 3 * k + 3 by omega]; exact chain e1 e2
    · rw [show o + y + 2 - 3 * ((k + 1 : ℕ) : ℤ) = o + y + 2 - 3 * (k : ℤ) - 3 by omega]; exact h2

/-! ### Phase 3: the growth cycles -/

/-- Block of ones on `(a, R]`, then `m` triples `0 0 1`, then a final `1` at `E`. -/
def CycP (a R : ℤ) (m : ℕ) (E i : ℤ) : Prop :=
  (a < i ∧ i ≤ R) ∨ (R < i ∧ i ≤ R + 3 * m ∧ (i - R) % 3 = 0) ∨ i = E

theorem cycle1 (a : ℤ) (n m : ℕ) (E : ℤ) (hE : E = a + n + 3 * (m + 1) + 1) (c : Config 5)
    (hc : Is c 0 a (CycP a (a + n) (m + 1) E)) :
    ∃ c', run BB5.winner c (2 * n + 8) = some c' ∧ Is c' 0 (a - 2) (CycP (a - 2) (a + n + 3) m E) := by
  obtain ⟨c1, e1, h1⟩ := sR1 (fun i => i = a ∨ CycP a (a + n) (m + 1) E i) hc
    (hc.read0 (by dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨c2, e2, h2⟩ := sweepB n c1 (a + 1) _ h1 (fun j hj => Or.inr (by dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega))))
  obtain ⟨c3, e3, h3⟩ := sR1 (fun i => i = a + 1 + n ∨ (i = a ∨ CycP a (a + n) (m + 1) E i)) h2
    (h2.read0 (by dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨c4, e4, h4⟩ := sR1 (fun i => i = a + 1 + n + 1 ∨
      (i = a + 1 + n ∨ (i = a ∨ CycP a (a + n) (m + 1) E i))) h3
    (h3.read0 (by dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨c5, e5, h5⟩ := sweepD (n + 4) c4 (a + 1 + n + 1 + 1) _ h4 (fun j hj => by dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega)))
  obtain ⟨c6, e6, h6⟩ := sL1 (fun i => i = a - 1 ∨ (i = a + 1 + n + 1 ∨
      (i = a + 1 + n ∨ (i = a ∨ CycP a (a + n) (m + 1) E i)))) h5
    (h5.read0 (by dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl
    (fun i => by rw [show a + 1 + (n : ℤ) + 1 + 1 - ((n + 4 : ℕ) : ℤ) = a - 1 by omega])
  refine ⟨c6, ?_, h6.1, by rw [h6.2.1]; omega, fun i => (h6.2.2 i).trans ?_⟩
  · rw [show 2 * n + 8 = 1 + n + 1 + 1 + (n + 4) + 1 by omega]
    exact chain1 (chain (chain1 (chain1 (chain (show run BB5.winner c 1 = some c1 from e1) e2) e3) e4) e5) e6
  · dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega))

def S : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, n => (2 * n + 8) + S m (n + 5)

theorem S_closed : ∀ m n : ℕ, S m n + 5 * m = m * (2 * n + 8) + 5 * (m * m) := by
  intro m
  induction m with
  | zero => intro n; simp [S]
  | succ m ih =>
    intro n
    have := ih (n + 5)
    simp only [S, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at this ⊢
    omega

theorem cycles : ∀ (m n : ℕ) (a E : ℤ) (c : Config 5), E = a + n + 3 * m + 1 →
    Is c 0 a (CycP a (a + n) m E) →
    ∃ c', run BB5.winner c (S m n) = some c' ∧ Is c' 0 (a - 2 * m) (CycP (a - 2 * m) (E - 1) 0 E) := by
  intro m
  induction m with
  | zero =>
    intro n a E c hE hc
    refine ⟨c, rfl, hc.1, by rw [hc.2.1]; omega, fun i => (hc.2.2 i).trans ?_⟩
    dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega))
  | succ m ih =>
    intro n a E c hE hc
    obtain ⟨c1, e1, h1⟩ := cycle1 a n m E (by omega) c hc
    obtain ⟨c2, e2, h2⟩ := ih (n + 5) (a - 2) E c1 (by omega)
      (h1.congr (fun i => by dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega))))
    refine ⟨c2, chain e1 e2, h2.1, by rw [h2.2.1]; omega, fun i => (h2.2.2 i).trans ?_⟩
    dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega))

/-! ### The three rules -/

theorem rule0 (o : ℤ) (x : ℕ) :
    run BB5.winner (G o (3 * x)) (5 * (x * x) + 19 * x + 15) = some (G (o - (2 * x + 3)) (5 * x + 6)) := by
  obtain ⟨c1, e1, h1⟩ := opening o (3 * x)
  obtain ⟨c2, e2, h2⟩ := loopK o (3 * x) (x + 1) c1 h1 (by omega)
  obtain ⟨c3, e3, h3⟩ := cycles (x + 1) 0 (o - 1) (o + 3 * x + 3) c2 (by omega)
    (h2.congr (fun i => by dsimp only [LoopP, CycP]; (first | omega | (constructor <;> intro hh <;> omega))) |> fun h => ⟨h.1, by rw [h.2.1]; omega, h.2.2⟩)
  have hS := S_closed (x + 1) 0
  have e := chain (chain e1 e2) e3
  rw [show 3 * x + 4 + 3 * (x + 1) + S (x + 1) 0 = 5 * (x * x) + 19 * x + 15 by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hS ⊢; omega] at e
  have h3' : Is c3 0 (o - (2 * x + 3)) _ := ⟨h3.1, by rw [h3.2.1]; omega, h3.2.2⟩
  rw [e, eq_G (y := 5 * x + 6) h3' (fun i => by dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega)))]

theorem rule1 (o : ℤ) (x : ℕ) :
    run BB5.winner (G o (3 * x + 1)) (5 * (x * x) + 25 * x + 27) = some (G (o - (2 * x + 5)) (5 * x + 9)) := by
  obtain ⟨c1, e1, h1⟩ := opening o (3 * x + 1)
  obtain ⟨c2, e2, h2⟩ := loopK o (3 * x + 1) (x + 1) c1 h1 (by omega)
  have h2' : Is c2 0 o (LoopP o (3 * x + 1) o) :=
    (h2.congr (fun i => by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) |> fun h => ⟨h.1, by rw [h.2.1]; omega, fun i => by
      rw [h.2.2 i]; dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega))⟩
  -- the 5-step kick: A1 → 1LC, C0 → 1RD, D1 → 1LD, D1 → 1LD, D0 → 1LA
  obtain ⟨k1, f1, g1⟩ := sL1 (fun i => i = o ∨ LoopP o (3 * x + 1) o i) h2'
    (h2'.read1 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨k2, f2, g2⟩ := sR1 (fun i => i = o - 1 ∨ (i = o ∨ LoopP o (3 * x + 1) o i)) g1
    (g1.read0 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨k3, f3, g3⟩ := sL1 (fun i => i = o - 1 + 1 ∨ (i = o - 1 ∨ (i = o ∨ LoopP o (3 * x + 1) o i))) g2
    (g2.read1 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨k4, f4, g4⟩ := sL1 (fun i => i = o - 1 + 1 - 1 ∨
      (i = o - 1 + 1 ∨ (i = o - 1 ∨ (i = o ∨ LoopP o (3 * x + 1) o i)))) g3
    (g3.read1 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨k5, f5, g5⟩ := sL1 (fun i => i = o - 1 + 1 - 1 - 1 ∨ (i = o - 1 + 1 - 1 ∨
      (i = o - 1 + 1 ∨ (i = o - 1 ∨ (i = o ∨ LoopP o (3 * x + 1) o i))))) g4
    (g4.read0 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  have ek : run BB5.winner c2 5 = some k5 :=
    chain1 (chain1 (chain1 (chain1 (show run BB5.winner c2 1 = some k1 from f1) f2) f3) f4) f5
  obtain ⟨c3, e3, h3⟩ := cycles (x + 1) 3 (o - 3) (o + 3 * x + 4) k5 (by omega)
    ⟨g5.1, by rw [g5.2.1]; omega, fun i => (g5.2.2 i).trans (by dsimp only [LoopP, CycP]; (first | omega | (constructor <;> intro hh <;> omega)))⟩
  have hS := S_closed (x + 1) 3
  have e := chain (chain (chain e1 e2) ek) e3
  rw [show 3 * x + 1 + 4 + 3 * (x + 1) + 5 + S (x + 1) 3 = 5 * (x * x) + 25 * x + 27 by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hS ⊢; omega] at e
  have h3' : Is c3 0 (o - (2 * x + 5)) _ := ⟨h3.1, by rw [h3.2.1]; omega, h3.2.2⟩
  rw [e, eq_G (y := 5 * x + 9) h3' (fun i => by dsimp only [CycP]; (first | omega | (constructor <;> intro hh <;> omega)))]

theorem rule2 (o : ℤ) (x : ℕ) :
    run BB5.winner (G o (3 * x + 2)) (6 * x + 12) = none ∧
      run BB5.winner (G o (3 * x + 2)) (6 * x + 11) ≠ none := by
  obtain ⟨c1, e1, h1⟩ := opening o (3 * x + 2)
  obtain ⟨c2, e2, h2⟩ := loopK o (3 * x + 2) (x + 1) c1 h1 (by omega)
  have h2' : Is c2 0 (o + 1) (LoopP o (3 * x + 2) (o + 1)) :=
    ⟨h2.1, by rw [h2.2.1]; omega, fun i => by rw [h2.2.2 i]; dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega))⟩
  obtain ⟨k1, f1, g1⟩ := sL1 (fun i => i = o + 1 ∨ LoopP o (3 * x + 2) (o + 1) i) h2'
    (h2'.read1 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  obtain ⟨k2, f2, g2⟩ := sL0 (fun i => i ≠ o + 1 - 1 ∧ (i = o + 1 ∨ LoopP o (3 * x + 2) (o + 1) i)) g1
    (g1.read1 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))) rfl (fun _ => Iff.rfl)
  have f3 : step BB5.winner k2 = none := sHalt g2 (by dsimp only [LoopP]; (first | omega | (constructor <;> intro hh <;> omega)))
  have e := chain e1 e2
  have a2 : run BB5.winner (G o (3 * x + 2)) (3 * x + 2 + 4 + 3 * (x + 1) + 1 + 1) = some k2 :=
    chain1 (chain1 e f1) f2
  constructor
  · rw [show 6 * x + 12 = 3 * x + 2 + 4 + 3 * (x + 1) + 1 + 1 + 1 by omega]
    show (run BB5.winner _ _).bind (step BB5.winner) = none
    rw [a2]; exact f3
  · rw [show 6 * x + 11 = 3 * x + 2 + 4 + 3 * (x + 1) + 1 + 1 by omega, a2]
    exact Option.some_ne_none _

end ChampAux

namespace ChampAux
open FCP.BusyBeaver

theorem R0 (o : ℤ) (x y n : ℕ) (o' : ℤ) (y' : ℕ) (hy : y = 3 * x) (hn : n = 5 * (x * x) + 19 * x + 15)
    (ho : o' = o - (2 * x + 3)) (hy' : y' = 5 * x + 6) : run BB5.winner (G o y) n = some (G o' y') := by
  subst hy hn ho hy'; exact rule0 o x

theorem R1 (o : ℤ) (x y n : ℕ) (o' : ℤ) (y' : ℕ) (hy : y = 3 * x + 1) (hn : n = 5 * (x * x) + 25 * x + 27)
    (ho : o' = o - (2 * x + 5)) (hy' : y' = 5 * x + 9) : run BB5.winner (G o y) n = some (G o' y') := by
  subst hy hn ho hy'; exact rule1 o x

theorem R2 (o : ℤ) (x y : ℕ) (hy : y = 3 * x + 2) :
    run BB5.winner (G o y) (6 * x + 12) = none ∧ run BB5.winner (G o y) (6 * x + 11) ≠ none := by
  subst hy; exact rule2 o x

theorem chainN {c d e : Config 5} {a b N : ℕ} (h1 : run BB5.winner c a = some d)
    (h2 : run BB5.winner d b = some e) (hN : a + b = N) : run BB5.winner c N = some e := by
  rw [← hN]; exact chain h1 h2

theorem init_eq : FCP.BusyBeaver.init (n := 5) (by omega) = G 0 0 :=
  eq_G (P := fun _ => False) ⟨rfl, rfl, fun _ => ⟨fun h => Bool.false_ne_true h, False.elim⟩⟩
    (fun i => ⟨False.elim, fun h => by omega⟩)

end ChampAux

theorem solution :
    FCP.BusyBeaver.HaltsIn BB5.winner (FCP.BusyBeaver.init (by omega)) 47176870 := by
  have s1 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 15 = some (ChampAux.G (-3) 6) :=
    ChampAux.R0 0 0 0 15 (-3) 6 (by decide) (by decide) (by decide) (by decide)
  have c1 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 15 = some (ChampAux.G (-3) 6) := s1
  have s2 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-3) 6) 73 = some (ChampAux.G (-10) 16) :=
    ChampAux.R0 (-3) 2 6 73 (-10) 16 (by decide) (by decide) (by decide) (by decide)
  have c2 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 88 = some (ChampAux.G (-10) 16) :=
    ChampAux.chainN c1 s2 (by decide)
  have s3 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-10) 16) 277 = some (ChampAux.G (-25) 34) :=
    ChampAux.R1 (-10) 5 16 277 (-25) 34 (by decide) (by decide) (by decide) (by decide)
  have c3 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 365 = some (ChampAux.G (-25) 34) :=
    ChampAux.chainN c2 s3 (by decide)
  have s4 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-25) 34) 907 = some (ChampAux.G (-52) 64) :=
    ChampAux.R1 (-25) 11 34 907 (-52) 64 (by decide) (by decide) (by decide) (by decide)
  have c4 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 1272 = some (ChampAux.G (-52) 64) :=
    ChampAux.chainN c3 s4 (by decide)
  have s5 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-52) 64) 2757 = some (ChampAux.G (-99) 114) :=
    ChampAux.R1 (-52) 21 64 2757 (-99) 114 (by decide) (by decide) (by decide) (by decide)
  have c5 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 4029 = some (ChampAux.G (-99) 114) :=
    ChampAux.chainN c4 s5 (by decide)
  have s6 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-99) 114) 7957 = some (ChampAux.G (-178) 196) :=
    ChampAux.R0 (-99) 38 114 7957 (-178) 196 (by decide) (by decide) (by decide) (by decide)
  have c6 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 11986 = some (ChampAux.G (-178) 196) :=
    ChampAux.chainN c5 s6 (by decide)
  have s7 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-178) 196) 22777 = some (ChampAux.G (-313) 334) :=
    ChampAux.R1 (-178) 65 196 22777 (-313) 334 (by decide) (by decide) (by decide) (by decide)
  have c7 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 34763 = some (ChampAux.G (-313) 334) :=
    ChampAux.chainN c6 s7 (by decide)
  have s8 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-313) 334) 64407 = some (ChampAux.G (-540) 564) :=
    ChampAux.R1 (-313) 111 334 64407 (-540) 564 (by decide) (by decide) (by decide) (by decide)
  have c8 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 99170 = some (ChampAux.G (-540) 564) :=
    ChampAux.chainN c7 s8 (by decide)
  have s9 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-540) 564) 180307 = some (ChampAux.G (-919) 946) :=
    ChampAux.R0 (-540) 188 564 180307 (-919) 946 (by decide) (by decide) (by decide) (by decide)
  have c9 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 279477 = some (ChampAux.G (-919) 946) :=
    ChampAux.chainN c8 s9 (by decide)
  have s10 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-919) 946) 504027 = some (ChampAux.G (-1554) 1584) :=
    ChampAux.R1 (-919) 315 946 504027 (-1554) 1584 (by decide) (by decide) (by decide) (by decide)
  have c10 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 783504 = some (ChampAux.G (-1554) 1584) :=
    ChampAux.chainN c9 s10 (by decide)
  have s11 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-1554) 1584) 1403967 = some (ChampAux.G (-2613) 2646) :=
    ChampAux.R0 (-1554) 528 1584 1403967 (-2613) 2646 (by decide) (by decide) (by decide) (by decide)
  have c11 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 2187471 = some (ChampAux.G (-2613) 2646) :=
    ChampAux.chainN c10 s11 (by decide)
  have s12 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-2613) 2646) 3906393 = some (ChampAux.G (-4380) 4416) :=
    ChampAux.R0 (-2613) 882 2646 3906393 (-4380) 4416 (by decide) (by decide) (by decide) (by decide)
  have c12 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 6093864 = some (ChampAux.G (-4380) 4416) :=
    ChampAux.chainN c11 s12 (by decide)
  have s13 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-4380) 4416) 10861903 = some (ChampAux.G (-7327) 7366) :=
    ChampAux.R0 (-4380) 1472 4416 10861903 (-7327) 7366 (by decide) (by decide) (by decide) (by decide)
  have c13 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 16955767 = some (ChampAux.G (-7327) 7366) :=
    ChampAux.chainN c12 s13 (by decide)
  have s14 : FCP.BusyBeaver.run BB5.winner (ChampAux.G (-7327) 7366) 30196527 = some (ChampAux.G (-12242) 12284) :=
    ChampAux.R1 (-7327) 2455 7366 30196527 (-12242) 12284 (by decide) (by decide) (by decide) (by decide)
  have c14 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 47152294 = some (ChampAux.G (-12242) 12284) :=
    ChampAux.chainN c13 s14 (by decide)
  obtain ⟨hz, hnz⟩ := ChampAux.R2 (-12242) 4094 12284 (by decide)
  rw [ChampAux.init_eq]
  have hT : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 47176870 = none := by
    rw [show 47176870 = 47152294 + (6 * 4094 + 12) by decide, ChampAux.run_trans _ _ _ _ c14]
    exact hz
  have hT1 : FCP.BusyBeaver.run BB5.winner (ChampAux.G 0 0) 47176869 ≠ none := by
    rw [show 47176869 = 47152294 + (6 * 4094 + 11) by decide, ChampAux.run_trans _ _ _ _ c14]
    exact hnz
  refine ⟨hT, fun s hs hsn => hT1 ?_⟩
  have := ChampAux.run_none _ _ s hsn (47176869 - s)
  rwa [show s + (47176869 - s) = 47176869 by omega] at this
