-- Prove2me | solution 1 for BB5.g_3x2
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-22T20:45:14.711652+00:00
-- url     : https://prove2.me/submissions/2c5fa0fa-49ec-41b3-9f8a-970bf6f9e868

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner
import Definitions.Def_BB5_gcfg

namespace G3Aux
open FCP.BusyBeaver

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

theorem run_step {n : ℕ} (M : TM n) (c d : Config n) (t : ℕ) (r : Option (Config n))
    (h : run M c t = some d) (hs : step M d = r) : run M c (t + 1) = r := by
  show (run M c t).bind (step M) = r
  rw [h]; exact hs

theorem step_L {n : ℕ} (M : TM n) (c : Config n) (w : Bool) (s : Fin n)
    (h : M.trans c.state (c.tape c.head) = (w, false, some s)) :
    step M c = some ⟨s, c.head - 1, Function.update c.tape c.head w⟩ := by
  unfold step; rw [h]; rfl

theorem step_R {n : ℕ} (M : TM n) (c : Config n) (w : Bool) (s : Fin n)
    (h : M.trans c.state (c.tape c.head) = (w, true, some s)) :
    step M c = some ⟨s, c.head + 1, Function.update c.tape c.head w⟩ := by
  unfold step; rw [h]; rfl

theorem step_H {n : ℕ} (M : TM n) (c : Config n) (w d : Bool)
    (h : M.trans c.state (c.tape c.head) = (w, d, none)) : step M c = none := by
  unfold step; rw [h]

theorem upd_ne (f : ℤ → Bool) (a i : ℤ) (v : Bool) (h : i ≠ a) : Function.update f a v i = f i := by
  rw [Function.update_apply, if_neg h]

theorem upd_same (f : ℤ → Bool) (a : ℤ) (h : f a = true) : Function.update f a true = f := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = a
  · rw [if_pos hi, hi, h]
  · rw [if_neg hi]

/-- State B sweeps right across a block of ones without changing the tape. -/
theorem sweepB : ∀ (m : ℕ) (c : Config 5), c.state = 1 →
    (∀ j : ℕ, j < m → c.tape (c.head + j) = true) →
    run BB5.winner c m = some ⟨1, c.head + m, c.tape⟩ := by
  intro m
  induction m with
  | zero =>
    intro c hs _
    obtain ⟨st, hd, tp⟩ := c
    simp only at hs
    subst hs
    show some _ = some _
    congr 1
    simp
  | succ m ih =>
    intro c hs hones
    have h0 : c.tape c.head = true := by simpa using hones 0 (by omega)
    have h1 : run BB5.winner c 1 = some ⟨1, c.head + 1, c.tape⟩ := by
      show step BB5.winner c = _
      rw [step_R BB5.winner c true 1 (by rw [hs, h0]; rfl), upd_same _ _ h0]
    have := run_trans BB5.winner c _ 1 h1 m
    rw [Nat.add_comm] at this
    rw [this, ih ⟨1, c.head + 1, c.tape⟩ rfl (by
      intro j hj
      have := hones (j + 1) (by omega)
      show c.tape (c.head + 1 + j) = true
      rw [show c.head + 1 + (j : ℤ) = c.head + ((j + 1 : ℕ) : ℤ) by omega]
      exact this)]
    show some _ = some _
    dsimp only
    congr 2
    omega

/-- Invariant of the leftward phase: state A at `p`, ones on `[0, p]`, blanks left of `0`. -/
def LInv (p : ℤ) (c : Config 5) : Prop :=
  c.state = 0 ∧ c.head = p ∧ (∀ i : ℤ, 0 ≤ i → i ≤ p → c.tape i = true) ∧
    (∀ i : ℤ, i < 0 → c.tape i = false)

theorem loop3 (p : ℤ) (c : Config 5) (hc : LInv p c) (hp : 2 ≤ p) :
    ∃ c', run BB5.winner c 3 = some c' ∧ LInv (p - 3) c' := by
  obtain ⟨hs, hh, hone, hneg⟩ := hc
  have r0 : c.tape c.head = true := by rw [hh]; exact hone p (by omega) (Int.le_refl _)
  let c1 : Config 5 := ⟨2, c.head - 1, Function.update c.tape c.head true⟩
  have e1 : step BB5.winner c = some c1 := step_L _ c true 2 (by rw [hs, r0]; rfl)
  have r1 : c1.tape c1.head = true := by
    show Function.update c.tape c.head true (c.head - 1) = true
    rw [upd_ne _ _ _ _ (by omega)]; rw [hh]; exact hone _ (by omega) (by omega)
  let c2 : Config 5 := ⟨4, c1.head - 1, Function.update c1.tape c1.head false⟩
  have e2 : step BB5.winner c1 = some c2 := step_L _ c1 false 4 (by rw [r1]; rfl)
  have r2 : c2.tape c2.head = true := by
    show Function.update (Function.update c.tape c.head true) (c.head - 1) false (c.head - 1 - 1) = true
    rw [upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega), hh]
    exact hone _ (by omega) (by omega)
  let c3 : Config 5 := ⟨0, c2.head - 1, Function.update c2.tape c2.head false⟩
  have e3 : step BB5.winner c2 = some c3 := step_L _ c2 false 0 (by rw [r2]; rfl)
  refine ⟨c3, ?_, rfl, ?_, ?_, ?_⟩
  · have a1 : run BB5.winner c 1 = some c1 := e1
    have a2 := run_step _ _ _ 1 _ a1 e2
    exact run_step _ _ _ 2 _ a2 e3
  · show c.head - 1 - 1 - 1 = p - 3
    omega
  · intro i hi0 hi
    show Function.update (Function.update (Function.update c.tape c.head true) (c.head - 1) false)
      (c.head - 1 - 1) false i = true
    rw [upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega)]
    exact hone i hi0 (by omega)
  · intro i hi
    show Function.update (Function.update (Function.update c.tape c.head true) (c.head - 1) false)
      (c.head - 1 - 1) false i = false
    rw [upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega)]
    exact hneg i hi

theorem loopK : ∀ (k : ℕ) (p : ℤ) (c : Config 5), LInv p c → 3 * (k : ℤ) ≤ p + 1 →
    ∃ c', run BB5.winner c (3 * k) = some c' ∧ LInv (p - 3 * k) c' := by
  intro k
  induction k with
  | zero => intro p c hc _; exact ⟨c, rfl, by simpa using hc⟩
  | succ k ih =>
    intro p c hc hk
    obtain ⟨c1, h1, hc1⟩ := loop3 p c hc (by omega)
    obtain ⟨c2, h2, hc2⟩ := ih (p - 3) c1 hc1 (by omega)
    refine ⟨c2, ?_, ?_⟩
    · rw [show 3 * (k + 1) = 3 + 3 * k by omega, run_trans _ c c1 3 h1]
      exact h2
    · rw [show p - 3 * ((k + 1 : ℕ) : ℤ) = p - 3 - 3 * (k : ℤ) by omega]
      exact hc2

/-- The final three steps from position `1`: the machine halts on the third. -/
theorem finish (c : Config 5) (hc : LInv 1 c) :
    run BB5.winner c 3 = none ∧ run BB5.winner c 2 ≠ none := by
  obtain ⟨hs, hh, hone, hneg⟩ := hc
  have r0 : c.tape c.head = true := by rw [hh]; exact hone 1 (by omega) (Int.le_refl _)
  let c1 : Config 5 := ⟨2, c.head - 1, Function.update c.tape c.head true⟩
  have e1 : step BB5.winner c = some c1 := step_L _ c true 2 (by rw [hs, r0]; rfl)
  have r1 : c1.tape c1.head = true := by
    show Function.update c.tape c.head true (c.head - 1) = true
    rw [upd_ne _ _ _ _ (by omega), hh]; exact hone _ (by omega) (by omega)
  let c2 : Config 5 := ⟨4, c1.head - 1, Function.update c1.tape c1.head false⟩
  have e2 : step BB5.winner c1 = some c2 := step_L _ c1 false 4 (by rw [r1]; rfl)
  have r2 : c2.tape c2.head = false := by
    show Function.update (Function.update c.tape c.head true) (c.head - 1) false (c.head - 1 - 1) = false
    rw [upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega), hh]
    exact hneg _ (by omega)
  have e3 : step BB5.winner c2 = none := step_H _ c2 false false (by rw [r2]; rfl)
  have a1 : run BB5.winner c 1 = some c1 := e1
  have a2 := run_step _ _ _ 1 _ a1 e2
  refine ⟨run_step _ _ _ 2 _ a2 e3, ?_⟩
  rw [a2]; exact Option.some_ne_none _

/-- The opening phase from `g(y)`: after `y + 4` steps the machine is in `LInv (y + 2)`. -/
theorem opening (y : ℕ) : ∃ c, run BB5.winner (BB5.gcfg y) (1 + y + 3) = some c ∧ LInv ((y : ℤ) + 2) c := by
  have g0 : (BB5.gcfg y).tape 0 = false := by
    show decide (1 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (y : ℤ)) = false; exact decide_eq_false (by omega)
  let c1 : Config 5 := ⟨1, 0 + 1, Function.update (BB5.gcfg y).tape 0 true⟩
  have a1 : run BB5.winner (BB5.gcfg y) 1 = some c1 :=
    step_R BB5.winner (BB5.gcfg y) true 1 (by rw [show (BB5.gcfg y).head = 0 from rfl, g0]; rfl)
  have sw := sweepB y c1 rfl (by
    intro j hj
    show Function.update (BB5.gcfg y).tape 0 true (0 + 1 + j) = true
    rw [upd_ne _ _ _ _ (by omega)]
    show decide (1 ≤ 0 + 1 + (j : ℤ) ∧ 0 + 1 + (j : ℤ) ≤ (y : ℤ)) = true
    exact decide_eq_true (by omega))
  have a2 := (run_trans _ _ _ 1 a1 y).trans sw
  -- tape after the sweep
  let T : ℤ → Bool := Function.update (BB5.gcfg y).tape 0 true
  have Tv : ∀ i : ℤ, T i = decide (0 ≤ i ∧ i ≤ (y : ℤ)) := by
    intro i
    show Function.update (BB5.gcfg y).tape 0 true i = _
    rw [Function.update_apply]
    by_cases hi : i = 0
    · rw [if_pos hi]; exact (decide_eq_true (by omega)).symm
    · rw [if_neg hi]; show decide (1 ≤ i ∧ i ≤ (y : ℤ)) = decide (0 ≤ i ∧ i ≤ (y : ℤ))
      by_cases h : 1 ≤ i ∧ i ≤ (y : ℤ)
      · rw [decide_eq_true h, decide_eq_true (by omega)]
      · rw [decide_eq_false h, decide_eq_false (by omega)]
  let d0 : Config 5 := ⟨1, 0 + 1 + (y : ℤ), T⟩
  have rd0 : d0.tape d0.head = false := by
    show T (0 + 1 + (y : ℤ)) = false; rw [Tv]; exact decide_eq_false (by omega)
  let d1 : Config 5 := ⟨2, d0.head + 1, Function.update d0.tape d0.head true⟩
  have e1 : step BB5.winner d0 = some d1 := step_R _ d0 true 2 (by rw [rd0]; rfl)
  have rd1 : d1.tape d1.head = false := by
    show Function.update T (0 + 1 + (y : ℤ)) true (0 + 1 + (y : ℤ) + 1) = false
    rw [upd_ne _ _ _ _ (by omega), Tv]; exact decide_eq_false (by omega)
  let d2 : Config 5 := ⟨3, d1.head + 1, Function.update d1.tape d1.head true⟩
  have e2 : step BB5.winner d1 = some d2 := step_R _ d1 true 3 (by rw [rd1]; rfl)
  have rd2 : d2.tape d2.head = false := by
    show Function.update (Function.update T (0 + 1 + (y : ℤ)) true) (0 + 1 + (y : ℤ) + 1) true
      (0 + 1 + (y : ℤ) + 1 + 1) = false
    rw [upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega), Tv]; exact decide_eq_false (by omega)
  let d3 : Config 5 := ⟨0, d2.head - 1, Function.update d2.tape d2.head true⟩
  have e3 : step BB5.winner d2 = some d3 := step_L _ d2 true 0 (by rw [rd2]; rfl)
  have b1 := run_step _ _ _ _ _ a2 e1
  have b2 := run_step _ _ _ _ _ b1 e2
  have b3 := run_step _ _ _ _ _ b2 e3
  refine ⟨d3, ?_, rfl, ?_, ?_, ?_⟩
  · rw [show 1 + y + 3 = 1 + y + 1 + 1 + 1 by omega]; exact b3
  · show 0 + 1 + (y : ℤ) + 1 + 1 - 1 = (y : ℤ) + 2
    omega
  · intro i hi0 hi
    show Function.update (Function.update (Function.update T (0 + 1 + (y : ℤ)) true)
      (0 + 1 + (y : ℤ) + 1) true) (0 + 1 + (y : ℤ) + 1 + 1) true i = true
    rw [Function.update_apply, Function.update_apply, Function.update_apply, Tv]
    by_cases h1 : i = 0 + 1 + (y : ℤ) + 1 + 1
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : i = 0 + 1 + (y : ℤ) + 1
      · rw [if_pos h2]
      · rw [if_neg h2]
        by_cases h3 : i = 0 + 1 + (y : ℤ)
        · rw [if_pos h3]
        · rw [if_neg h3]; exact decide_eq_true (by omega)
  · intro i hi
    show Function.update (Function.update (Function.update T (0 + 1 + (y : ℤ)) true)
      (0 + 1 + (y : ℤ) + 1) true) (0 + 1 + (y : ℤ) + 1 + 1) true i = false
    rw [upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega), upd_ne _ _ _ _ (by omega), Tv]
    exact decide_eq_false (by omega)

end G3Aux

theorem solution (x : ℕ) :
    FCP.BusyBeaver.HaltsIn BB5.winner (BB5.gcfg (3 * x + 2)) (6 * x + 12) := by
  obtain ⟨a, ha, hia⟩ := G3Aux.opening (3 * x + 2)
  obtain ⟨b, hb, hib⟩ := G3Aux.loopK (x + 1) _ a hia (by omega)
  have hib' : G3Aux.LInv 1 b := by
    rw [show ((3 * x + 2 : ℕ) : ℤ) + 2 - 3 * ((x + 1 : ℕ) : ℤ) = 1 by omega] at hib
    exact hib
  obtain ⟨hn, hs⟩ := G3Aux.finish b hib'
  have hab := (G3Aux.run_trans _ _ _ _ ha (3 * (x + 1))).trans hb
  have hT : FCP.BusyBeaver.run BB5.winner (BB5.gcfg (3 * x + 2)) (6 * x + 12) = none := by
    rw [show 6 * x + 12 = (1 + (3 * x + 2) + 3 + 3 * (x + 1)) + 3 by omega,
      G3Aux.run_trans _ _ _ _ hab 3]
    exact hn
  have hT1 : FCP.BusyBeaver.run BB5.winner (BB5.gcfg (3 * x + 2)) (6 * x + 11) ≠ none := by
    rw [show 6 * x + 11 = (1 + (3 * x + 2) + 3 + 3 * (x + 1)) + 2 by omega,
      G3Aux.run_trans _ _ _ _ hab 2]
    exact hs
  refine ⟨hT, ?_⟩
  intro s hs' hsn
  apply hT1
  have := G3Aux.run_none _ _ s hsn (6 * x + 11 - s)
  rwa [show s + (6 * x + 11 - s) = 6 * x + 11 by omega] at this
