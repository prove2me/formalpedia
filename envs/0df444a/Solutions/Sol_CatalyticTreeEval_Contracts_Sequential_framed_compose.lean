-- Prove2me | solution 1 for CatalyticTreeEval.Contracts.Sequential.framed_compose
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T01:54:07.771346+00:00
-- url     : https://prove2.me/submissions/c56b3de3-1431-4578-ab10-0a11db7fcbd3

import Definitions.Def_CatalyticTreeEval_SequentialMachine
import Definitions.Def_CatalyticTreeEval_MachineContracts


set_option autoImplicit false

namespace CatalyticTreeEval.Contracts

universe u

@[simp] theorem runFrom_zero {C : Type u} (step : C → Option C) (c : C) :
    runFrom step c 0 = some c := rfl

@[simp] theorem runFrom_succ {C : Type u} (step : C → Option C) (c : C) (t : ℕ) :
    runFrom step c (t + 1) = (runFrom step c t).bind step := rfl

/-- Composition preserves failures rather than silently treating them as halts. -/
theorem runFrom_add {C : Type u} (step : C → Option C) (c : C) (s t : ℕ) :
    runFrom step c (s + t) = (runFrom step c s).bind (fun d => runFrom step d t) := by
  induction t with
  | zero => simp
  | succ t ih => simp [runFrom, ih, Option.bind_assoc]

/-- The wrapper agrees with the mission's initialized semantics at every time. -/
theorem runFrom_initial (M : Main.Machine) (input τ : List Bool) (t : ℕ) :
    runFrom (M.step input) (M.initial τ) t = M.run input τ t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [runFrom_succ, CatalyticMatching.General.Machine.run, ih]

theorem Segment.at {C : Type u} {step : C → Option C} {inv : ℕ → C → Prop}
    {a b : C} {T : ℕ} (H : Segment step inv a b T) {t : ℕ} (ht : t ≤ T) :
    ∃ c, runFrom step a t = some c ∧ inv t c := by
  cases hr : runFrom step a t with
  | none =>
      have h := H.result
      rw [show T = t + (T - t) by omega, runFrom_add, hr] at h
      simp at h
  | some c => exact ⟨c, rfl, H.during t ht c hr⟩

theorem Segment.weaken {C : Type u} {step : C → Option C}
    {I J : ℕ → C → Prop} {a b : C} {T : ℕ} (H : Segment step I a b T)
    (hIJ : ∀ t ≤ T, ∀ c, I t c → J t c) : Segment step J a b T where
  result := H.result
  during t ht c hc := hIJ t ht c (H.during t ht c hc)

/-- Same-machine segments concatenate with additive exact time, including zero
length segments. The second invariant is shifted by the first segment's time. -/
theorem Segment.trans {C : Type u} {step : C → Option C}
    {I J K : ℕ → C → Prop} {a b c : C} {s t : ℕ}
    (A : Segment step I a b s) (B : Segment step J b c t)
    (hA : ∀ u ≤ s, ∀ d, I u d → K u d)
    (hB : ∀ u ≤ t, ∀ d, J u d → K (s + u) d) :
    Segment step K a c (s + t) where
  result := by rw [runFrom_add, A.result]; exact B.result
  during u hu d hd := by
    by_cases h : u ≤ s
    · exact hA u h d (A.during u h d hd)
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (by omega : s ≤ u)
      rw [runFrom_add, A.result] at hd
      exact hB v (by omega) d (B.during v (by omega) d (by simpa using hd))

/-- A later exit must also be avoided throughout the first phase. Omitting this
premise would make first-exit composition false even when both runs succeed. -/
theorem FirstExit.trans {C : Type u} {step : C → Option C}
    {I J K : ℕ → C → Prop} {X Y : Set C} {a b c : C} {s t : ℕ}
    (A : FirstExit step I X a b s) (B : FirstExit step J Y b c t)
    (hA : ∀ u ≤ s, ∀ d, I u d → K u d)
    (hB : ∀ u ≤ t, ∀ d, J u d → K (s + u) d)
    (avoid : ∀ u < s, ∀ d, runFrom step a u = some d → d ∉ Y) :
    FirstExit step K Y a c (s + t) where
  toSegment := A.toSegment.trans B.toSegment hA hB
  exit_mem := B.exit_mem
  cut u hu d hd := by
    by_cases h : u < s
    · exact avoid u h d hd
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (by omega : s ≤ u)
      rw [runFrom_add, A.result] at hd
      exact B.cut v (by omega) d (by simpa using hd)

theorem FirstExit.time_eq {C : Type u} {step : C → Option C}
    {I J : ℕ → C → Prop} {X : Set C} {a b c : C} {s t : ℕ}
    (A : FirstExit step I X a b s) (B : FirstExit step J X a c t) : s = t := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact B.cut s hlt b A.result A.exit_mem
  · exact A.cut t hgt c B.result B.exit_mem

theorem Envelope.contains_hull_left {M : Main.Machine} {A B : Envelope}
    {c : Config M} (h : A.Contains c) : (A.hull B).Contains c := by
  rcases h with ⟨h1,h2,h3,h4⟩
  simp only [Envelope.Contains, Envelope.hull]
  omega

theorem Envelope.contains_hull_right {M : Main.Machine} {A B : Envelope}
    {c : Config M} (h : B.Contains c) : (A.hull B).Contains c := by
  rcases h with ⟨h1,h2,h3,h4⟩
  simp only [Envelope.Contains, Envelope.hull]
  omega

theorem SameOutside.refl {M : Main.Machine} (F : Footprint) (c : Config M) :
    SameOutside F c c := ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩

theorem SameOutside.mono {M : Main.Machine} {A B : Footprint} {a b : Config M}
    (H : SameOutside A a b) (hw : A.work ⊆ B.work) (hc : A.catalyst ⊆ B.catalyst) :
    SameOutside B a b :=
  ⟨fun p hp => H.1 p (fun h => hp (hw h)), H.2.1,
   fun p hp => H.2.2 p (fun h => hp (hc h))⟩

theorem SameOutside.trans {M : Main.Machine} {A B : Footprint}
    {a b c : Config M} (hA : SameOutside A a b) (hB : SameOutside B b c) :
    SameOutside (A.union B) a c := by
  refine ⟨?_, hB.2.1.trans hA.2.1, ?_⟩
  · intro p hp
    exact (hB.1 p (fun h => hp (Or.inr h))).trans (hA.1 p (fun h => hp (Or.inl h)))
  · intro p hp
    exact (hB.2.2 p (fun h => hp (Or.inr h))).trans (hA.2.2 p (fun h => hp (Or.inl h)))

theorem SameOutside.savedPrefix {M : Main.Machine} {F : Footprint}
    {a b : Config M} (H : SameOutside F a b) (r : ℕ)
    (disjoint : ∀ p < r, p ∉ F.work) : SavedPrefix r a b := by
  intro p hp
  exact H.1 p (disjoint p hp)

/-- The trajectory frame, head envelope, and exact time compose together. The
second frame is relative to the actual intermediate configuration. -/
theorem Segment.framed_trans {M : Main.Machine} {input : List Bool}
    {EA EB : Envelope} {FA FB : Footprint} {a b c : Config M} {s t : ℕ}
    (A : Segment (M.step input) (fun _ d => EA.Contains d ∧ SameOutside FA a d) a b s)
    (B : Segment (M.step input) (fun _ d => EB.Contains d ∧ SameOutside FB b d) b c t) :
    Segment (M.step input)
      (fun _ d => (EA.hull EB).Contains d ∧ SameOutside (FA.union FB) a d)
      a c (s + t) := by
  have hab := (A.during s le_rfl b A.result).2
  apply A.trans B
  · intro u hu d hd
    exact ⟨Envelope.contains_hull_left hd.1,
      hd.2.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h)⟩
  · intro u hu d hd
    exact ⟨Envelope.contains_hull_right hd.1, hab.trans hd.2⟩

/-- From the contract's actual execution to the platform's timed printer goal. -/
theorem Contract.printsIn {M : Main.Machine} {ι : Type} (C : Contract M ι) (i : ι)
    (hentry : C.entry = M.start) (hpre : C.pre i (M.initial []))
    (hhalt : (C.post i (M.initial [])).state = none)
    (output : List Bool) (hout : C.emitted i (M.initial []) = output)
    (space time : ℝ)
    (hspace : (C.envelope i (M.initial [])).workHi ≤ ⌈space⌉₊)
    (htime : (C.time i (M.initial []) : ℝ) ≤ time) :
    Main.PrintsIn M (C.input i) output space time := by
  have hstart : (M.initial []).state = some C.entry := by
    simp [CatalyticMatching.General.Machine.initial, hentry]
  have H := C.executes i (M.initial []) hstart hpre
  refine ⟨C.time i (M.initial []), C.post i (M.initial []), ?_, hhalt, ?_, ?_, htime⟩
  · simpa only [runFrom_initial] using H.result
  · rw [C.output_eq i _ hstart hpre, hout]
    rfl
  · intro u hu c hc
    have hr : runFrom (M.step (C.input i)) (M.initial []) u = some c := by
      simpa only [runFrom_initial] using hc
    exact ((H.during u hu c hr).1.2.1).trans_le hspace

/-- The source's space-only printer interface does not need a supplied time
bound. The contract still certifies the number of actual transitions. -/
theorem Contract.prints {M : Main.Machine} {ι : Type} (C : Contract M ι) (i : ι)
    (hentry : C.entry = M.start) (hpre : C.pre i (M.initial []))
    (hhalt : (C.post i (M.initial [])).state = none)
    (output : List Bool) (hout : C.emitted i (M.initial []) = output)
    (space : ℝ) (hspace : (C.envelope i (M.initial [])).workHi ≤ ⌈space⌉₊) :
    Main.Prints M (C.input i) output space := by
  obtain ⟨t, c, hr, hh, ho, hw, _⟩ :=
    C.printsIn i hentry hpre hhalt output hout space (C.time i (M.initial [])) hspace le_rfl
  exact ⟨t, c, hr, hh, ho, hw⟩

/-- Native catalytic correctness, including the head bound at every intermediate
configuration, follows from a uniform family of initialized contracts. -/
theorem Contract.computesPrefix {M : Main.Machine} {ι : Type} (C : Contract M ι) (i : ι)
    (hentry : C.entry = M.start) (output : List Bool) (space catalyst time : ℝ)
    (hpre : ∀ τ : List Bool, ⌈catalyst⌉₊ ≤ τ.length → C.pre i (M.initial τ))
    (hhalt : ∀ τ : List Bool, ⌈catalyst⌉₊ ≤ τ.length →
      (C.post i (M.initial τ)).state = none)
    (hout : ∀ τ : List Bool, ⌈catalyst⌉₊ ≤ τ.length →
      C.emitted i (M.initial τ) = output)
    (hrestore : ∀ τ : List Bool, ⌈catalyst⌉₊ ≤ τ.length →
      (C.post i (M.initial τ)).catalyst = τ)
    (hspace : ∀ τ : List Bool, ⌈catalyst⌉₊ ≤ τ.length →
      (C.envelope i (M.initial τ)).workHi ≤ ⌈space⌉₊)
    (hcatalyst : ∀ τ : List Bool, ⌈catalyst⌉₊ ≤ τ.length →
      (C.envelope i (M.initial τ)).catalystHi ≤ ⌈catalyst⌉₊)
    (htime : ∀ τ : List Bool, ⌈catalyst⌉₊ ≤ τ.length →
      (C.time i (M.initial τ) : ℝ) ≤ time) :
    Main.ComputesPrefix M (C.input i) output space catalyst time := by
  intro τ hτ
  have hstart : (M.initial τ).state = some C.entry := by
    simp [CatalyticMatching.General.Machine.initial, hentry]
  have H := C.executes i (M.initial τ) hstart (hpre τ hτ)
  refine ⟨C.time i (M.initial τ), C.post i (M.initial τ), ?_, hhalt τ hτ,
    ?_, hrestore τ hτ, ?_, htime τ hτ, ?_⟩
  · simpa only [runFrom_initial] using H.result
  · rw [C.output_eq i _ hstart (hpre τ hτ), hout τ hτ]
    rfl
  · intro u hu c hc
    have hr : runFrom (M.step (C.input i)) (M.initial τ) u = some c := by
      simpa only [runFrom_initial] using hc
    exact ((H.during u hu c hr).1.2.1).trans_le (hspace τ hτ)
  · intro u hu c hc
    have hr : runFrom (M.step (C.input i)) (M.initial τ) u = some c := by
      simpa only [runFrom_initial] using hc
    exact ((H.during u hu c hr).1.2.2.2).trans_le (hcatalyst τ hτ)

end CatalyticTreeEval.Contracts


set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.Sequential

open CatalyticMatching.General

theorem step_left (A B : Machine) (input : List Bool) (c : Configuration A)
    (live : c.state ≠ none) :
    (machine A B).step input (leftConfig A B c) =
      (A.step input c).map (leftConfig A B) := by
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases hs : state with
    | none => exact False.elim (live hs)
    | some q =>
      simp only [Machine.step, leftConfig, machine, leftState, Equiv.symm_apply_apply,
        Option.elim_some, leftInstruction]
      try dsimp only
      split_ifs <;> simp_all [leftConfig]

theorem step_right (A B : Machine) (input : List Bool) (c : Configuration B) :
    (machine A B).step input (rightConfig A B c) =
      (B.step input c).map (rightConfig A B) := by
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases hs : state with
    | none => rfl
    | some q =>
      simp only [Machine.step, rightConfig, machine, rightState, Equiv.symm_apply_apply,
        Option.map_some, rightInstruction]
      try dsimp only
      split_ifs <;> simp_all [rightConfig]

theorem handoff_eq (A B : Machine) (c : Configuration A) (halt : c.state = none) :
    leftConfig A B c = rightConfig A B (handoff A B c) := by
  cases c
  cases halt
  rfl

theorem initial_left (A B : Machine) (τ : List Bool) :
    (machine A B).initial τ = leftConfig A B (A.initial τ) := rfl

theorem runFrom_right (A B : Machine) (input : List Bool) (c : Configuration B) (t : ℕ) :
    runFrom ((machine A B).step input) (rightConfig A B c) t =
      (runFrom (B.step input) c t).map (rightConfig A B) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runFrom_succ, runFrom_succ, ih]
      cases hr : runFrom (B.step input) c t with
      | none => rfl
      | some d => simpa using step_right A B input d

/-- Through A's first halt, its exact successful or failing prefixes are
preserved by the finite-control host. The live-prefix hypothesis prevents
mistaking an absorbing halt for an additional A transition. -/
theorem runFrom_left_prefix (A B : Machine) (input : List Bool) (c : Configuration A)
    (T : ℕ)
    (live : ∀ u < T, ∀ d, runFrom (A.step input) c u = some d → d.state ≠ none) :
    ∀ u ≤ T, runFrom ((machine A B).step input) (leftConfig A B c) u =
      (runFrom (A.step input) c u).map (leftConfig A B) := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
      intro hu
      rw [runFrom_succ, runFrom_succ, ih (by omega)]
      cases hr : runFrom (A.step input) c u with
      | none => rfl
      | some d => simpa using step_left A B input d (live u (by omega) d hr)

/-- Actual machine composition with additive transition count. B runs on
exactly A's final physical configuration, with no assumed tape reset. -/
theorem runFrom_compose (A B : Machine) (input : List Bool)
    (c a : Configuration A) (b : Configuration B) (s t : ℕ)
    (ha : runFrom (A.step input) c s = some a)
    (halt : a.state = none)
    (live : ∀ u < s, ∀ d, runFrom (A.step input) c u = some d → d.state ≠ none)
    (hb : runFrom (B.step input) (handoff A B a) t = some b) :
    runFrom ((machine A B).step input) (leftConfig A B c) (s + t) =
      some (rightConfig A B b) := by
  have hs := runFrom_left_prefix A B input c s live s le_rfl
  rw [ha, Option.map_some, handoff_eq A B a halt] at hs
  rw [runFrom_add, hs]
  simpa only [Option.bind_some, runFrom_right, hb, Option.map_some]

/-- Initialized runs use the same composite finite table; only the first
machine gets a blank work tape. -/
theorem initialized_compose (A B : Machine) (input τ : List Bool)
    (a : Configuration A) (b : Configuration B) (s t : ℕ)
    (ha : A.run input τ s = some a) (halt : a.state = none)
    (live : ∀ u < s, ∀ d, A.run input τ u = some d → d.state ≠ none)
    (hb : runFrom (B.step input) (handoff A B a) t = some b) :
    (machine A B).run input τ (s + t) = some (rightConfig A B b) := by
  rw [← runFrom_initial, initial_left]
  apply runFrom_compose A B input (A.initial τ) a b s t
  · simpa only [runFrom_initial] using ha
  · exact halt
  · simpa only [runFrom_initial] using live
  · exact hb

/-- Trajectory invariants transfer phase by phase, including the final heads.
This rule is used to transport head envelopes, output and memory frames to the
actual composite finite machine, rather than merely adding time annotations. -/
theorem framed_compose (A B : Machine) (input : List Bool)
    {c a : Configuration A} {b : Configuration B} {s t : ℕ}
    {IA : ℕ → Configuration A → Prop} {IB : ℕ → Configuration B → Prop}
    {I : ℕ → Configuration (machine A B) → Prop}
    (HA : Segment (A.step input) IA c a s)
    (HB : Segment (B.step input) IB (handoff A B a) b t)
    (halt : a.state = none)
    (live : ∀ u < s, ∀ d, runFrom (A.step input) c u = some d → d.state ≠ none)
    (hA : ∀ u ≤ s, ∀ d, IA u d → I u (leftConfig A B d))
    (hB : ∀ u ≤ t, ∀ d, IB u d → I (s + u) (rightConfig A B d)) :
    Segment ((machine A B).step input) I (leftConfig A B c) (rightConfig A B b) (s + t) where
  result := runFrom_compose A B input c a b s t HA.result halt live HB.result
  during u hu d hd := by
    by_cases h : u ≤ s
    · rw [runFrom_left_prefix A B input c s live u h] at hd
      cases hr : runFrom (A.step input) c u with
      | none => simp [hr] at hd
      | some p =>
          have heq : leftConfig A B p = d := by simpa [hr] using hd
          rw [← heq]
          exact hA u h p (HA.during u h p hr)
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (by omega : s ≤ u)
      have hs := runFrom_left_prefix A B input c s live s le_rfl
      rw [HA.result, Option.map_some, handoff_eq A B a halt] at hs
      rw [runFrom_add, hs] at hd
      change runFrom ((machine A B).step input) (rightConfig A B (handoff A B a)) v = some d at hd
      rw [runFrom_right] at hd
      cases hr : runFrom (B.step input) (handoff A B a) v with
      | none => simp [hr] at hd
      | some p =>
          have heq : rightConfig A B p = d := by simpa [hr] using hd
          rw [← heq]
          exact hB v (by omega) p (HB.during v (by omega) p hr)

end CatalyticTreeEval.Contracts.Sequential

open CatalyticTreeEval.Contracts CatalyticTreeEval.Contracts.Sequential CatalyticMatching.General

theorem solution (A B : Machine) (input : List Bool)
    {c a : Configuration A} {b : Configuration B} {s t : ℕ}
    {IA : ℕ → Configuration A → Prop} {IB : ℕ → Configuration B → Prop}
    {I : ℕ → Configuration (machine A B) → Prop}
    (HA : Segment (A.step input) IA c a s)
    (HB : Segment (B.step input) IB (handoff A B a) b t)
    (halt : a.state = none)
    (live : ∀ u < s, ∀ d, runFrom (A.step input) c u = some d → d.state ≠ none)
    (hA : ∀ u ≤ s, ∀ d, IA u d → I u (leftConfig A B d))
    (hB : ∀ u ≤ t, ∀ d, IB u d → I (s + u) (rightConfig A B d)) :
    Segment ((machine A B).step input) I (leftConfig A B c) (rightConfig A B b) (s + t) := by
  exact framed_compose A B input HA HB halt live hA hB
