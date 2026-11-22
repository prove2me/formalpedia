-- Prove2me | solution 1 for BB5.upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-22T15:44:14.964936+00:00
-- url     : https://prove2.me/submissions/f738bec8-d10f-4a09-9d5e-f93564f6a3e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Theorems.Thm_BB5_no_halt_RA
import Theorems.Thm_BB5_halt_le_0RB
import Theorems.Thm_BB5_halt_le_1RB

open FCP.BusyBeaver

private lemma config_mk_inj {n : ℕ} {a b : Config n}
    (hs : a.state = b.state) (hh : a.head = b.head) (ht : a.tape = b.tape) : a = b := by
  cases a
  cases b
  simp_all

private lemma init_proof_irrel {n : ℕ} (h₁ h₂ : 0 < n) : init h₁ = init h₂ := by
  simp [init]

/-- The halting time from a fixed configuration is unique. -/
private lemma halts_time_unique {n : ℕ} {M : TM n} {c : Config n} {t₁ t₂ : ℕ}
    (h₁ : HaltsIn M c t₁) (h₂ : HaltsIn M c t₂) : t₁ = t₂ := by
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · exact (h₂.2 t₁ hlt h₁.1).elim
  · exact heq
  · exact (h₁.2 t₂ hgt h₂.1).elim

/-- Extract the bound from a child theorem's disjunctive conclusion. -/
private lemma bound_from_child {M : TM 5} {t : ℕ}
    (hhal : HaltsIn M (init (by omega)) t)
    (hc : (∀ t : ℕ, run M (init (by omega)) t ≠ none) ∨
          (∃ t : ℕ, t ≤ 47176870 ∧ HaltsIn M (init (by omega)) t)) :
    t ≤ 47176870 := by
  rcases hc with hnohalt | ⟨t', ht'b, ht'hal⟩
  · exact (hnohalt t hhal.1).elim
  · have ht_eq : t = t' := halts_time_unique hhal ht'hal
    omega

-- ---------------- State relabelling ----------------

private def relabelTM (σ : Equiv.Perm (Fin 5)) (M : TM 5) : TM 5 :=
  ⟨fun q b =>
    match M.trans (σ.symm q) b with
    | (w, d, none) => (w, d, none)
    | (w, d, some s) => (w, d, some (σ s))⟩

private def relabelConfig (σ : Equiv.Perm (Fin 5)) (c : Config 5) : Config 5 :=
  ⟨σ c.state, c.head, c.tape⟩

private lemma step_relabel (σ : Equiv.Perm (Fin 5)) (M : TM 5) (c : Config 5) :
    step (relabelTM σ M) (relabelConfig σ c) = (step M c).map (relabelConfig σ) := by
  rcases h : M.trans c.state (c.tape c.head) with ⟨w, d, _ | s⟩
  · simp [step, relabelTM, relabelConfig, h]
  · simp [step, relabelTM, relabelConfig, h]

private lemma run_relabel (σ : Equiv.Perm (Fin 5)) (M : TM 5) (c : Config 5) :
    ∀ t, run (relabelTM σ M) (relabelConfig σ c) t = (run M c t).map (relabelConfig σ)
  | 0 => by simp [run, relabelConfig]
  | t + 1 => by
      rw [run, run, run_relabel σ M c t]
      cases h : run M c t with
      | none => simp
      | some c' => simp [step_relabel]

private lemma halts_relabel (σ : Equiv.Perm (Fin 5))
    (hσ0 : σ (0 : Fin 5) = (0 : Fin 5))
    (M : TM 5) (t : ℕ) (h : HaltsIn M (init (by omega)) t) :
    HaltsIn (relabelTM σ M) (init (by omega)) t := by
  have hinit : relabelConfig σ (init (by omega)) = init (by omega) := by
    apply config_mk_inj <;> simp [relabelConfig, init, hσ0]
  constructor
  · rw [← hinit, run_relabel]
    simp [h.1]
  · intro s hs
    rw [← hinit, run_relabel]
    simpa using h.2 s hs

/-- Relabel a machine whose A0 goes right to a state C/D/E, so that A0 goes to B. -/
private lemma bound_of_A0_right_CDE (M : TM 5) (t : ℕ) (w : Bool) (s : Fin 5)
    (hs0 : s ≠ (0 : Fin 5)) (_hs1 : s ≠ (1 : Fin 5))
    (hA0 : M.trans (0 : Fin 5) false = (w, true, some s))
    (hhal : HaltsIn M (init (by omega)) t) : t ≤ 47176870 := by
  let σ : Equiv.Perm (Fin 5) := Equiv.swap (1 : Fin 5) s
  have h0s : (0 : Fin 5) ≠ s := fun h0s => hs0 h0s.symm
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  have hσ0 : σ (0 : Fin 5) = 0 := by
    exact Equiv.swap_apply_of_ne_of_ne h01 h0s
  have hσs : σ s = 1 := by
    exact Equiv.swap_apply_right (1 : Fin 5) s
  have hσsymm0 : σ.symm (0 : Fin 5) = 0 := by
    simpa using (congrArg σ.symm hσ0).symm
  have hmir : HaltsIn (relabelTM σ M) (init (by omega)) t := halts_relabel σ hσ0 M t hhal
  have hA0gen : (relabelTM σ M).trans (0 : Fin 5) false = (w, true, some (1 : Fin 5)) := by
    simp [relabelTM, hσsymm0, hA0, hσs]
  cases w with
  | false =>
      have hA0' : (relabelTM σ M).trans (0 : Fin 5) false = (false, true, some (1 : Fin 5)) := by
        simpa using hA0gen
      exact bound_from_child hmir (BB5.halt_le_0RB (relabelTM σ M) hA0')
  | true =>
      have hA0' : (relabelTM σ M).trans (0 : Fin 5) false = (true, true, some (1 : Fin 5)) := by
        simpa using hA0gen
      exact bound_from_child hmir (BB5.halt_le_1RB (relabelTM σ M) hA0')

-- ---------------- Tape mirror ----------------

private def mirrorTM (M : TM 5) : TM 5 :=
  ⟨fun s b =>
    match M.trans s b with
    | (w, d, s') => (w, !d, s')⟩

private def mirrorConfig (c : Config 5) : Config 5 :=
  ⟨c.state, -c.head, fun i => c.tape (-i)⟩

private lemma step_mirror (M : TM 5) (c : Config 5) :
    step (mirrorTM M) (mirrorConfig c) = (step M c).map mirrorConfig := by
  rcases h : M.trans c.state (c.tape c.head) with ⟨w, d, _ | s'⟩
  · simp [step, mirrorTM, mirrorConfig, h]
  · simp [step, mirrorTM, mirrorConfig, h]
    constructor
    · cases d <;> simp <;> omega
    · apply funext
      intro i
      by_cases hi : i = -c.head
      · subst hi
        simp
      · have hi' : -i ≠ c.head := by
          intro hh
          apply hi
          omega
        simp [hi, hi']

private lemma run_mirror (M : TM 5) (c : Config 5) :
    ∀ t, run (mirrorTM M) (mirrorConfig c) t = (run M c t).map mirrorConfig
  | 0 => by simp [run, mirrorConfig]
  | t + 1 => by
      rw [run, run, run_mirror M c t]
      cases h : run M c t with
      | none => simp
      | some c' => simp [step_mirror]

private lemma halts_mirror (M : TM 5) (t : ℕ) (h : HaltsIn M (init (by omega)) t) :
    HaltsIn (mirrorTM M) (init (by omega)) t := by
  have hinit : mirrorConfig (init (by omega)) = init (by omega) := by
    apply config_mk_inj
    · simp [mirrorConfig, init]
    · simp [mirrorConfig, init]
    · apply funext
      intro i
      simp [mirrorConfig, init]
  constructor
  · rw [← hinit, run_mirror]
    simp [h.1]
  · intro s hs
    rw [← hinit, run_mirror]
    simpa using h.2 s hs

-- ---------------- A0 goes right: main case analysis ----------------

private lemma bound_of_A0_right (M : TM 5) (t : ℕ)
    (hhal : HaltsIn M (init (by omega)) t)
    (hd : (M.trans (0 : Fin 5) false).2.1 = true) : t ≤ 47176870 := by
  rcases h : M.trans (0 : Fin 5) false with ⟨w, d, sn⟩
  have hd' : d = true := by
    rw [h] at hd
    exact hd
  subst d
  rcases sn with _ | s
  · -- A0 halts immediately: the halting time is exactly 1.
    have hstep1 : run M (init (by omega)) 1 = none := by
      simp [run, step, init, h]
    have htpos : 0 < t := by
      by_contra hn
      have ht0 : t = 0 := by omega
      subst t
      have hne : run M (init (by omega)) 0 ≠ none := by simp [run]
      exact hne hhal.1
    have htle1 : t ≤ 1 := by
      by_contra hn
      have hgt : 1 < t := by omega
      have hne : run M (init (by omega)) 1 ≠ none := hhal.2 1 hgt
      exact hne hstep1
    omega
  · fin_cases s
    · -- next state A: 0RA or 1RA never halts, contradicting hhal.
      have hnohalt : ∀ t : ℕ, run M (init (by omega)) t ≠ none := by
        apply BB5.no_halt_RA M
        constructor <;> simp [h]
      exact (hnohalt t hhal.1).elim
    · -- next state B: 0RB or 1RB.
      cases w with
      | false => exact bound_from_child hhal (BB5.halt_le_0RB M (by simpa [h]))
      | true => exact bound_from_child hhal (BB5.halt_le_1RB M (by simpa [h]))
    · -- next state C: relabel C to B.
      exact bound_of_A0_right_CDE M t w (2 : Fin 5) (by decide) (by decide) (by simpa [h]) hhal
    · -- next state D: relabel D to B.
      exact bound_of_A0_right_CDE M t w (3 : Fin 5) (by decide) (by decide) (by simpa [h]) hhal
    · -- next state E: relabel E to B.
      exact bound_of_A0_right_CDE M t w (4 : Fin 5) (by decide) (by decide) (by simpa [h]) hhal

-- ---------------- The upper bound ----------------

theorem solution : FCP.BusyBeaver.BB 5 ≤ 47176870 := by
  rw [FCP.BusyBeaver.BB]
  apply csSup_le'
  intro t ht
  rcases ht with ⟨M, hpos, hhal0⟩
  have hhal : HaltsIn M (init (by omega)) t := by
    simpa [init_proof_irrel] using hhal0
  rcases h : M.trans (0 : Fin 5) false with ⟨w, d, sn⟩
  cases d with
  | false =>
      -- A0 goes left: mirror the tape so A0 goes right.
      have hmir : HaltsIn (mirrorTM M) (init (by omega)) t := halts_mirror M t hhal
      have hmir_right : ((mirrorTM M).trans (0 : Fin 5) false).2.1 = true := by
        simp [mirrorTM, h]
      exact bound_of_A0_right (mirrorTM M) t hmir hmir_right
  | true =>
      exact bound_of_A0_right M t hhal (by simp [h])
