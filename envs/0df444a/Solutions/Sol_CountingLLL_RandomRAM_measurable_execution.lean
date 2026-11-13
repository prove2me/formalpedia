-- Prove2me | solution 1 for CountingLLL.RandomRAM.measurable_execution
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:04:56.29276+00:00
-- url     : https://prove2.me/submissions/eb8af201-4663-4d0f-8921-e01b9d8da279

import Definitions.Def_CountingLLL_RandomSpec

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Classical
open CountingLLL.RandomRAM

private theorem step_ext (Φ : CSP) (P : Program) (ω ω' : Tape) (s : State)
    (h : ω s.used = ω' s.used) : step Φ P ω s = step Φ P ω' s := by
  unfold step
  split <;> simp_all

private theorem step_used (Φ : CSP) (P : Program) (ω : Tape) (s : State) :
    (step Φ P ω s).used ≤ s.used + 1 := by
  unfold step
  split <;> simp_all
  split <;> simp_all

private theorem run_ext_used (Φ : CSP) (P : Program) (ω ω' : Tape) (t : ℕ) :
    ∀ s : State, (∀ i < s.used + t, ω i = ω' i) →
      run Φ P ω s t = run Φ P ω' s t ∧ (run Φ P ω s t).used ≤ s.used + t := by
  induction t with
  | zero =>
    intro s h
    simp [run]
  | succ t ih =>
    intro s h
    have heq : step Φ P ω s = step Φ P ω' s := step_ext Φ P ω ω' s (h s.used (by omega))
    have hbound := step_used Φ P ω s
    have hprefix : ∀ i < (step Φ P ω s).used + t, ω i = ω' i := by
      intro i hi
      exact h i (by omega)
    have hh := ih (step Φ P ω s) hprefix
    constructor
    · simpa [run, Function.iterate_succ_apply, heq] using hh.1
    · simpa [run, Function.iterate_succ_apply] using (show
        (run Φ P ω (step Φ P ω s) t).used ≤ s.used + (t + 1) by omega)

private theorem prefix_event_measurable (n : ℕ) (S : Set Tape)
    (hS : ∀ ω ω', (∀ i < n, ω i = ω' i) → (ω ∈ S ↔ ω' ∈ S)) :
    MeasurableSet S := by
  let pref : Tape → (Fin n → Bool) := fun ω i => ω i.val
  have hm : Measurable pref := measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  let T : Set (Fin n → Bool) := {p | ∃ ω ∈ S, pref ω = p}
  have heq : S = pref ⁻¹' T := by
    ext ω
    constructor
    · intro hω
      exact ⟨ω, hω, rfl⟩
    · rintro ⟨ω', hω', hpre⟩
      have hpre' : ∀ i < n, ω i = ω' i := by
        intro i hi
        exact (congrFun hpre ⟨i, hi⟩).symm
      exact (hS ω ω' hpre').2 hω'
  rw [heq]
  exact MeasurableSet.of_discrete.preimage hm

/-- Every predicate of the state after t steps is determined by a finite tape prefix. -/
theorem measurable_run_event (Φ : CSP) (P : Program) (s : State) (t : ℕ)
    (A : State → Prop) : MeasurableSet {ω | A (run Φ P ω s t)} := by
  apply prefix_event_measurable (s.used + t)
  intro ω ω' h
  have heq := (run_ext_used Φ P ω ω' t s h).1
  simp only [Set.mem_setOf_eq, heq]

/-- Termination is a countable union of finite-time halt events. -/
theorem measurable_halts (Φ : CSP) (P : Program) (s : State) :
    MeasurableSet {ω | Halts Φ P ω s} := by
  have heq : {ω | Halts Φ P ω s} =
      ⋃ t : ℕ, {ω | (run Φ P ω s t).base.out.isSome} := by
    ext ω
    simp [Halts]
  rw [heq]
  exact MeasurableSet.iUnion (fun t => measurable_run_event Φ P s t (fun st => st.base.out.isSome = true))

/-- The first-halting state, including its default value on divergent tapes, has measurable
preimage for every predicate on machine states. -/
theorem measurable_final_event (Φ : CSP) (P : Program) (s : State) (A : State → Prop) :
    MeasurableSet {ω | A (finalState Φ P ω s)} := by
  classical
  let first : ℕ → State → Prop := fun t st => st.base.out.isSome
  let events : ℕ → Set Tape := fun t => {ω |
    (run Φ P ω s t).base.out.isSome ∧
    (∀ j < t, ¬ (run Φ P ω s j).base.out.isSome) ∧ A (run Φ P ω s t)}
  have hevents : ∀ t, MeasurableSet (events t) := by
    intro t
    have h1 := measurable_run_event Φ P s t (fun st => st.base.out.isSome ∧ A st)
    have h2 : MeasurableSet (⋂ j : Fin t, {ω | ¬ (run Φ P ω s j.val).base.out.isSome}) :=
      MeasurableSet.iInter fun j => measurable_run_event Φ P s j.val (fun st => ¬ st.base.out.isSome = true)
    have heq : events t = {ω | (run Φ P ω s t).base.out.isSome ∧ A (run Φ P ω s t)} ∩
        (⋂ j : Fin t, {ω | ¬ (run Φ P ω s j.val).base.out.isSome}) := by
      ext ω
      simp only [events, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h, hmin, hA⟩
        exact ⟨⟨h, hA⟩, fun j => hmin j.val j.isLt⟩
      · rintro ⟨⟨h, hA⟩, hmin⟩
        exact ⟨h, fun j hj => hmin ⟨j, hj⟩, hA⟩
    rw [heq]
    exact h1.inter h2
  have heq : {ω | A (finalState Φ P ω s)} =
      (({ω | Halts Φ P ω s}ᶜ) ∩ {ω | A s}) ∪ ⋃ t, events t := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_iUnion, events]
    constructor
    · intro hA
      by_cases h : Halts Φ P ω s
      · right
        refine ⟨Nat.find h, Nat.find_spec h, ?_, ?_⟩
        · intro j hj
          exact Nat.find_min h hj
        · simpa [finalState, h] using hA
      · left
        exact ⟨h, by simpa [finalState, h] using hA⟩
    · rintro (⟨h, hA⟩ | ⟨t, ht, hmin, hA⟩)
      · simpa [finalState, h] using hA
      · have h : Halts Φ P ω s := ⟨t, ht⟩
        have hfind : Nat.find h = t := (Nat.find_eq_iff h).mpr ⟨ht, hmin⟩
        simpa [finalState, h, hfind] using hA
  rw [heq]
  exact ((measurable_halts Φ P s).compl.inter (by by_cases h : A s <;> simp [h])) |>.union
    (MeasurableSet.iUnion hevents)

private theorem measurable_cost_fn (Φ : CSP) (P : Program) (s : State)
    (g : State → ℝ≥0∞) :
    Measurable (fun ω => if Halts Φ P ω s then g (finalState Φ P ω s) else ⊤) := by
  classical
  intro T hT
  have heq : (fun ω => if Halts Φ P ω s then g (finalState Φ P ω s) else ⊤) ⁻¹' T =
      ({ω | Halts Φ P ω s} ∩ {ω | g (finalState Φ P ω s) ∈ T}) ∪
      (if ⊤ ∈ T then {ω | Halts Φ P ω s}ᶜ else ∅) := by
    ext ω
    by_cases h : Halts Φ P ω s <;> by_cases htop : (⊤ : ℝ≥0∞) ∈ T <;>
      simp [h, htop]
  rw [heq]
  have h1 := (measurable_halts Φ P s).inter (measurable_final_event Φ P s (fun st => g st ∈ T))
  have h2 : MeasurableSet (if ⊤ ∈ T then {ω | Halts Φ P ω s}ᶜ else ∅) := by
    by_cases h : (⊤ : ℝ≥0∞) ∈ T <;> simp [h, measurable_halts Φ P s]
  exact h1.union h2

theorem measurable_oracle_cost (Φ : CSP) (P : Program) (s : State) :
    Measurable (fun ω => oracleCost Φ P ω s) := by
  classical
  exact measurable_cost_fn Φ P s (fun st => (st.base.oracle : ℝ≥0∞))

theorem measurable_time_cost (Φ : CSP) (P : Program) (s : State) :
    Measurable (fun ω => timeCost Φ P ω s) := by
  classical
  exact measurable_cost_fn Φ P s (fun st => (st.base.time : ℝ≥0∞))

theorem measurable_output_event (Φ : CSP) (P : Program) (s : State) (x : Φ.Config) :
    MeasurableSet {ω | Halts Φ P ω s ∧ OutputConfig Φ (finalState Φ P ω s) x} :=
  (measurable_halts Φ P s).inter (measurable_final_event Φ P s (fun st => OutputConfig Φ st x))

theorem measurable_count_success (Φ : CSP) (P : Program) (s : ℕ) :
    MeasurableSet (countSuccess Φ P s) := by
  exact (measurable_halts Φ P (countingStart Φ s)).inter
    (measurable_final_event Φ P (countingStart Φ s) (fun st =>
      ∃ a b : ℤ, st.base.out = some (a,b) ∧ 0 < b ∧
        (1 - epsilon s) * Φ.ZPhi ≤ (a : ℝ) / b ∧
        (a : ℝ) / b ≤ (1 + epsilon s) * Φ.ZPhi))

theorem solution :
    (∀ (Φ : CSP) (P : Program) (s : State),
      MeasurableSet {ω | Halts Φ P ω s} ∧
      (∀ A : State → Prop, MeasurableSet {ω | A (finalState Φ P ω s)}) ∧
      Measurable (fun ω => oracleCost Φ P ω s) ∧
      Measurable (fun ω => timeCost Φ P ω s) ∧
      (∀ x : Φ.Config, MeasurableSet {ω | Halts Φ P ω s ∧
        OutputConfig Φ (finalState Φ P ω s) x})) ∧
    (∀ (Φ : CSP) (P : Program) (n : ℕ), MeasurableSet (countSuccess Φ P n)) := by
  constructor
  · intro Φ P s
    exact ⟨measurable_halts Φ P s, measurable_final_event Φ P s,
      measurable_oracle_cost Φ P s, measurable_time_cost Φ P s,
      measurable_output_event Φ P s⟩
  · exact measurable_count_success
