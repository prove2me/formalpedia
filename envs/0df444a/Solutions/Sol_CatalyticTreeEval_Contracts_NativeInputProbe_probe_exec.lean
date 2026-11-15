-- Prove2me | solution 1 for CatalyticTreeEval.Contracts.NativeInputProbe.probe_exec
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T15:13:53.836738+00:00
-- url     : https://prove2.me/submissions/37b78aa5-802d-49a2-aa9c-3eb4760c0660

import Definitions.Def_CatalyticTreeEval_NativeBufferedInput

/- Proof source: Solutions.CatalyticTreeEvaluation.MachineContractLaws -/
section

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

theorem Segment.single {C : Type u} {step : C → Option C} {I : ℕ → C → Prop}
    {a b : C} (transition : step a = some b) (entry : I 0 a) (exit : I 1 b) :
    Segment step I a b 1 where
  result := transition
  during t ht d hd := by
    cases t with
    | zero =>
        have heq : a = d := by simpa only [runFrom_zero, Option.some.injEq] using hd
        simpa only [← heq] using entry
    | succ t =>
        have heq : t = 0 := by omega
        subst t
        have hd' : b = d := Option.some.inj (transition.symm.trans hd)
        simpa only [← hd'] using exit

/-- Finite-control embeddings preserve failures as well as successful steps. -/
theorem runFrom_map {C D : Type u} (step : C → Option C) (step' : D → Option D)
    (embed : C → D) (commutes : ∀ c, step' (embed c) = (step c).map embed)
    (c : C) (t : ℕ) :
    runFrom step' (embed c) t = (runFrom step c t).map embed := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runFrom_succ, runFrom_succ, ih]
      cases hr : runFrom step c t with
      | none => rfl
      | some d => simpa using commutes d

theorem Segment.map {C D : Type u} {step : C → Option C} {step' : D → Option D}
    {IA : ℕ → C → Prop} {I : ℕ → D → Prop} {a b : C} {t : ℕ}
    (H : Segment step IA a b t) (embed : C → D)
    (commutes : ∀ c, step' (embed c) = (step c).map embed)
    (lift : ∀ u ≤ t, ∀ c, IA u c → I u (embed c)) :
    Segment step' I (embed a) (embed b) t where
  result := by rw [runFrom_map step step' embed commutes, H.result]; rfl
  during u hu d hd := by
    rw [runFrom_map step step' embed commutes] at hd
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hd
    exact lift u hu c (H.during u hu c hc)

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

/-- Before a first exit, no two successful prefixes can have the same
configuration. A repetition would give an earlier route to the final exit. -/
theorem FirstExit.time_injective {C : Type u} {step : C → Option C}
    {I : ℕ → C → Prop} {X : Set C} {a b : C} {T : ℕ}
    (H : FirstExit step I X a b T) {s t : ℕ} (hs : s ≤ T) (ht : t ≤ T)
    {c : C} (at_s : runFrom step a s = some c) (at_t : runFrom step a t = some c) :
    s = t := by
  suffices ordered : ∀ s t, s < t → t ≤ T → runFrom step a s = some c →
      runFrom step a t = some c → False by
    rcases lt_trichotomy s t with h | h | h
    · exact False.elim (ordered s t h ht at_s at_t)
    · exact h
    · exact False.elim (ordered t s h hs at_t at_s)
  intro s t hst ht hs ht'
  have tail : runFrom step c (T - t) = some b := by
    have h := H.result
    rw [show T = t + (T - t) by omega, runFrom_add, ht'] at h
    exact h
  have earlier : runFrom step a (s + (T - t)) = some b := by
    rw [runFrom_add, hs]
    exact tail
  exact H.cut (s + (T - t)) (by omega) b earlier H.exit_mem

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
end

/- Proof source: Solutions.CatalyticTreeEvaluation.SequentialMachineLaws -/
section

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

theorem firstExit_compose (A B : Machine) (input : List Bool)
    {c a : Configuration A} {b : Configuration B} {s t : ℕ}
    {IA : ℕ → Configuration A → Prop} {IB : ℕ → Configuration B → Prop}
    {I : ℕ → Configuration (machine A B) → Prop}
    (HA : FirstExit (A.step input) IA {d | d.state = none} c a s)
    (HB : FirstExit (B.step input) IB {d | d.state = none} (handoff A B a) b t)
    (hA : ∀ u ≤ s, ∀ d, IA u d → I u (leftConfig A B d))
    (hB : ∀ u ≤ t, ∀ d, IB u d → I (s + u) (rightConfig A B d)) :
    FirstExit ((machine A B).step input) I {d | d.state = none}
      (leftConfig A B c) (rightConfig A B b) (s + t) where
  toSegment := framed_compose A B input HA.toSegment HB.toSegment HA.exit_mem
    (fun u hu d hd => HA.cut u hu d hd) hA hB
  exit_mem := by simpa [rightConfig] using HB.exit_mem
  cut u hu d hd := by
    by_cases early : u < s
    · rw [runFrom_left_prefix A B input c s
        (fun v hv e he => HA.cut v hv e he) u (by omega)] at hd
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hd
      simp [leftConfig]
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (by omega : s ≤ u)
      have hs := runFrom_left_prefix A B input c s
        (fun v hv e he => HA.cut v hv e he) s le_rfl
      rw [HA.result, Option.map_some, handoff_eq A B a HA.exit_mem] at hs
      rw [runFrom_add, hs] at hd
      change runFrom ((machine A B).step input) (rightConfig A B (handoff A B a)) v = some d at hd
      rw [runFrom_right] at hd
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hd
      simpa [rightConfig] using HB.cut v (by omega) p hp

end CatalyticTreeEval.Contracts.Sequential
end

/- Proof source: Solutions.CatalyticTreeEvaluation.BranchMachineLaws -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.Branch

open CatalyticMatching.General

theorem step_left (A B : Machine) (input : List Bool) (c : Configuration A) :
    (machine A B).step input (leftConfig A B c) = (A.step input c).map (leftConfig A B) := by
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases state with
    | none => rfl
    | some q =>
      simp only [Machine.step, leftConfig, machine, leftState, Equiv.symm_apply_apply,
        Option.map_some, leftInstruction]
      try dsimp only
      split_ifs <;> simp_all [leftConfig]

theorem step_right (A B : Machine) (input : List Bool) (c : Configuration B) :
    (machine A B).step input (rightConfig A B c) = (B.step input c).map (rightConfig A B) := by
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases state with
    | none => rfl
    | some q =>
      simp only [Machine.step, rightConfig, machine, rightState, Equiv.symm_apply_apply,
        Option.map_some, rightInstruction]
      try dsimp only
      split_ifs <;> simp_all [rightConfig]

theorem step_true (A B : Machine) (input : List Bool) (c : Configuration A)
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    (machine A B).step input (gateConfig A B c) = some (leftConfig A B (startLeft A c)) := by
  cases c
  simp_all [Machine.step, gateConfig, machine, gateState, gateInstruction, startLeft,
    leftConfig, Move.apply]

theorem step_false (A B : Machine) (input : List Bool) (c : Configuration A)
    (flag : c.work c.workHead = false)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    (machine A B).step input (gateConfig A B c) = some (rightConfig A B (startRight A B c)) := by
  cases c
  simp_all [Machine.step, gateConfig, machine, gateState, gateInstruction, startRight,
    rightConfig, Move.apply]

theorem run_left (A B : Machine) (input : List Bool) (c : Configuration A) (t : ℕ) :
    runFrom ((machine A B).step input) (leftConfig A B c) t =
      (runFrom (A.step input) c t).map (leftConfig A B) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runFrom_succ, runFrom_succ, ih]
      cases hr : runFrom (A.step input) c t with
      | none => rfl
      | some d => simpa using step_left A B input d

theorem run_right (A B : Machine) (input : List Bool) (c : Configuration B) (t : ℕ) :
    runFrom ((machine A B).step input) (rightConfig A B c) t =
      (runFrom (B.step input) c t).map (rightConfig A B) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runFrom_succ, runFrom_succ, ih]
      cases hr : runFrom (B.step input) c t with
      | none => rfl
      | some d => simpa using step_right A B input d

theorem run_true (A B : Machine) (input : List Bool) (c a : Configuration A) (t : ℕ)
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (body : runFrom (A.step input) (startLeft A c) t = some a) :
    runFrom ((machine A B).step input) (gateConfig A B c) (1 + t) = some (leftConfig A B a) := by
  rw [runFrom_add]
  simp only [runFrom_succ, runFrom_zero, Option.bind_some]
  rw [step_true A B input c flag hi hc]
  simp only [Option.bind_some, run_left, body, Option.map_some]

theorem run_false (A B : Machine) (input : List Bool) (c : Configuration A)
    (b : Configuration B) (t : ℕ)
    (flag : c.work c.workHead = false)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (body : runFrom (B.step input) (startRight A B c) t = some b) :
    runFrom ((machine A B).step input) (gateConfig A B c) (1 + t) = some (rightConfig A B b) := by
  rw [runFrom_add]
  simp only [runFrom_succ, runFrom_zero, Option.bind_some]
  rw [step_false A B input c flag hi hc]
  simp only [Option.bind_some, run_right, body, Option.map_some]

theorem framed_true (A B : Machine) (input : List Bool) (c a : Configuration A)
    {IA : ℕ → Configuration A → Prop} {I : ℕ → Configuration (machine A B) → Prop} {t : ℕ}
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (body : Segment (A.step input) IA (startLeft A c) a t)
    (entry : I 0 (gateConfig A B c))
    (lift : ∀ u ≤ t, ∀ d, IA u d → I (1 + u) (leftConfig A B d)) :
    Segment ((machine A B).step input) I (gateConfig A B c) (leftConfig A B a) (1 + t) := by
  have hstart := body.during 0 (Nat.zero_le t) (startLeft A c) rfl
  have dispatch : Segment ((machine A B).step input) I
      (gateConfig A B c) (leftConfig A B (startLeft A c)) 1 :=
    Segment.single (step_true A B input c flag hi hc) entry (lift 0 (Nat.zero_le t) _ hstart)
  have H : Segment ((machine A B).step input) (fun u d => I (1 + u) d)
      (leftConfig A B (startLeft A c)) (leftConfig A B a) t :=
    body.map (leftConfig A B) (step_left A B input) lift
  exact dispatch.trans H (fun _ _ _ h => h) (fun _ _ _ h => h)

theorem framed_false (A B : Machine) (input : List Bool) (c : Configuration A)
    (b : Configuration B)
    {IB : ℕ → Configuration B → Prop} {I : ℕ → Configuration (machine A B) → Prop} {t : ℕ}
    (flag : c.work c.workHead = false)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (body : Segment (B.step input) IB (startRight A B c) b t)
    (entry : I 0 (gateConfig A B c))
    (lift : ∀ u ≤ t, ∀ d, IB u d → I (1 + u) (rightConfig A B d)) :
    Segment ((machine A B).step input) I (gateConfig A B c) (rightConfig A B b) (1 + t) := by
  have hstart := body.during 0 (Nat.zero_le t) (startRight A B c) rfl
  have dispatch : Segment ((machine A B).step input) I
      (gateConfig A B c) (rightConfig A B (startRight A B c)) 1 :=
    Segment.single (step_false A B input c flag hi hc) entry (lift 0 (Nat.zero_le t) _ hstart)
  have H : Segment ((machine A B).step input) (fun u d => I (1 + u) d)
      (rightConfig A B (startRight A B c)) (rightConfig A B b) t :=
    body.map (rightConfig A B) (step_right A B input) lift
  exact dispatch.trans H (fun _ _ _ h => h) (fun _ _ _ h => h)

theorem firstExit_true (A B : Machine) (input : List Bool) (c a : Configuration A)
    {IA : ℕ → Configuration A → Prop} {I : ℕ → Configuration (machine A B) → Prop} {t : ℕ}
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (body : FirstExit (A.step input) IA {d | d.state = none} (startLeft A c) a t)
    (entry : I 0 (gateConfig A B c))
    (lift : ∀ u ≤ t, ∀ d, IA u d → I (1 + u) (leftConfig A B d)) :
    FirstExit ((machine A B).step input) I {d | d.state = none}
      (gateConfig A B c) (leftConfig A B a) (1 + t) where
  toSegment := framed_true A B input c a flag hi hc body.toSegment entry lift
  exit_mem := by simpa [leftConfig] using body.exit_mem
  cut u hu d hd := by
    cases u with
    | zero =>
        have heq : gateConfig A B c = d := by simpa only [runFrom_zero, Option.some.injEq] using hd
        rw [← heq]
        simp [gateConfig]
    | succ u =>
        rw [show u + 1 = 1 + u by omega, runFrom_add] at hd
        simp only [runFrom_succ, runFrom_zero, Option.bind_some] at hd
        rw [step_true A B input c flag hi hc] at hd
        simp only [Option.bind_some, run_left] at hd
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hd
        simpa [leftConfig] using body.cut u (by omega) p hp

theorem firstExit_false (A B : Machine) (input : List Bool) (c : Configuration A)
    (b : Configuration B)
    {IB : ℕ → Configuration B → Prop} {I : ℕ → Configuration (machine A B) → Prop} {t : ℕ}
    (flag : c.work c.workHead = false)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (body : FirstExit (B.step input) IB {d | d.state = none} (startRight A B c) b t)
    (entry : I 0 (gateConfig A B c))
    (lift : ∀ u ≤ t, ∀ d, IB u d → I (1 + u) (rightConfig A B d)) :
    FirstExit ((machine A B).step input) I {d | d.state = none}
      (gateConfig A B c) (rightConfig A B b) (1 + t) where
  toSegment := framed_false A B input c b flag hi hc body.toSegment entry lift
  exit_mem := by simpa [rightConfig] using body.exit_mem
  cut u hu d hd := by
    cases u with
    | zero =>
        have heq : gateConfig A B c = d := by simpa only [runFrom_zero, Option.some.injEq] using hd
        rw [← heq]
        simp [gateConfig]
    | succ u =>
        rw [show u + 1 = 1 + u by omega, runFrom_add] at hd
        simp only [runFrom_succ, runFrom_zero, Option.bind_some] at hd
        rw [step_false A B input c flag hi hc] at hd
        simp only [Option.bind_some, run_right] at hd
        obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hd
        simpa [rightConfig] using body.cut u (by omega) p hp

end CatalyticTreeEval.Contracts.Branch
end

/- Proof source: Solutions.CatalyticTreeEvaluation.ReentryMachineLaws -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.Reentry

open CatalyticMatching.General

theorem step (A : Machine) (entry : Fin A.states) (input : List Bool) (c : Configuration A) :
    (machine A entry).step input (config A entry c) = (A.step input c).map (config A entry) := by
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases state with
    | none => rfl
    | some q =>
      simp only [Machine.step, config, machine]
      try dsimp only
      split_ifs <;> simp_all [config]

theorem run (A : Machine) (entry : Fin A.states) (input : List Bool)
    (c : Configuration A) (t : ℕ) :
    runFrom ((machine A entry).step input) (config A entry c) t =
      (runFrom (A.step input) c t).map (config A entry) :=
  runFrom_map (A.step input) ((machine A entry).step input) (config A entry)
    (step A entry input) c t

theorem initialized (A : Machine) (entry : Fin A.states) (input tape : List Bool) (t : ℕ) :
    (machine A entry).run input tape t =
      (runFrom (A.step input) { A.initial tape with state := some entry } t).map (config A entry) := by
  rw [← runFrom_initial]
  exact run A entry input { A.initial tape with state := some entry } t

theorem framed (A : Machine) (entry : Fin A.states) (input : List Bool)
    {IA : ℕ → Configuration A → Prop}
    {I : ℕ → Configuration (machine A entry) → Prop}
    {c d : Configuration A} {t : ℕ}
    (body : Segment (A.step input) IA c d t)
    (lift : ∀ u ≤ t, ∀ e, IA u e → I u (config A entry e)) :
    Segment ((machine A entry).step input) I (config A entry c) (config A entry d) t :=
  body.map (config A entry) (step A entry input) lift

theorem firstExit (A : Machine) (entry : Fin A.states) (input : List Bool)
    {IA : ℕ → Configuration A → Prop}
    {I : ℕ → Configuration (machine A entry) → Prop}
    {c d : Configuration A} {t : ℕ}
    (body : FirstExit (A.step input) IA {e | e.state = none} c d t)
    (lift : ∀ u ≤ t, ∀ e, IA u e → I u (config A entry e)) :
    FirstExit ((machine A entry).step input) I {e | e.state = none}
      (config A entry c) (config A entry d) t where
  toSegment := framed A entry input body.toSegment lift
  exit_mem := body.exit_mem
  cut u hu e he := by
    rw [run] at he
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    exact body.cut u hu a ha

end CatalyticTreeEval.Contracts.Reentry
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeRoundSupport -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeRoundSupport

open CatalyticMatching.General

/-- Reuse physical data while selecting a finite native machine's start port. -/
def startOn {N : Main.Machine} (M : Main.Machine) (c : Config N) : Config M :=
  { c with state := some M.start }

def enterOn {N : Main.Machine} (M : Main.Machine) (entry : Fin M.states)
    (c : Config N) : Config M := { c with state := some entry }

theorem forget {C : Type} {step : C → Option C} {I : ℕ → C → Prop}
    {X : Set C} {c d : C} {t : ℕ} (H : FirstExit step I X c d t) :
    FirstExit step (fun _ _ => True) X c d t where
  result := H.result
  during _ _ _ _ := True.intro
  exit_mem := H.exit_mem
  cut := H.cut

theorem seq {N : Main.Machine} (A B : Main.Machine) (input : List Bool) (c : Config N)
    (a : Config A) (b : Config B) (s t : ℕ)
    (HA : FirstExit (A.step input) (fun _ _ => True) {d | d.state = none}
      (startOn A c) a s)
    (HB : FirstExit (B.step input) (fun _ _ => True) {d | d.state = none}
      (startOn B a) b t) :
    FirstExit ((Sequential.machine A B).step input) (fun _ _ => True) {d | d.state = none}
      (startOn (Sequential.machine A B) c) (Sequential.rightConfig A B b) (s + t) := by
  change FirstExit _ _ _ (Sequential.leftConfig A B (startOn A c)) _ _
  exact Sequential.firstExit_compose A B input HA HB
    (fun _ _ _ _ => True.intro) (fun _ _ _ _ => True.intro)

theorem branch_true {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (a : Config A) (t : ℕ)
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (HA : FirstExit (A.step input) (fun _ _ => True) {d | d.state = none}
      (startOn A c) a t) :
    FirstExit ((Branch.machine A B).step input) (fun _ _ => True) {d | d.state = none}
      (startOn (Branch.machine A B) c) (Branch.leftConfig A B a) (1 + t) := by
  change FirstExit _ _ _ (Branch.gateConfig A B (startOn A c)) _ _
  exact Branch.firstExit_true A B input (startOn A c) a flag hi hc HA True.intro
    (fun _ _ _ _ => True.intro)

theorem branch_false {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (b : Config B) (t : ℕ)
    (flag : c.work c.workHead = false)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (HB : FirstExit (B.step input) (fun _ _ => True) {d | d.state = none}
      (startOn B c) b t) :
    FirstExit ((Branch.machine A B).step input) (fun _ _ => True) {d | d.state = none}
      (startOn (Branch.machine A B) c) (Branch.rightConfig A B b) (1 + t) := by
  change FirstExit _ _ _ (Branch.gateConfig A B (startOn A c)) _ _
  exact Branch.firstExit_false A B input (startOn A c) b flag hi hc HB True.intro
    (fun _ _ _ _ => True.intro)

theorem reentry {N : Main.Machine} (A : Main.Machine) (entry : Fin A.states)
    (input : List Bool) (c : Config N) (a : Config A) (t : ℕ)
    (HA : FirstExit (A.step input) (fun _ _ => True) {d | d.state = none}
      (enterOn A entry c) a t) :
    FirstExit ((Reentry.machine A entry).step input) (fun _ _ => True) {d | d.state = none}
      (startOn (Reentry.machine A entry) c) (Reentry.config A entry a) t where
  result := by
    change runFrom _ (Reentry.config A entry (enterOn A entry c)) _ = _
    rw [Reentry.run, HA.result]
    rfl
  during _ _ _ _ := True.intro
  exit_mem := by simpa [Reentry.config] using HA.exit_mem
  cut u hu d hd := by
    change runFrom _ (Reentry.config A entry (enterOn A entry c)) u = some d at hd
    rw [Reentry.run] at hd
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hd
    simpa [Reentry.config] using HA.cut u hu p hp

end CatalyticTreeEval.Contracts.NativeRoundSupport
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeVisits -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeRoundSupport

/-- Charged work cells include every prefix and the final head. -/
def Visits {M : Main.Machine} (input : List Bool) (c : Config M) (time bound : ℕ) : Prop :=
  ∀ u ≤ time, ∀ d, runFrom (M.step input) c u = some d → d.workHead < bound

theorem Visits.mono {M : Main.Machine} {input : List Bool} {c : Config M}
    {time small large : ℕ} (H : Visits input c time small) (h : small ≤ large) :
    Visits input c time large := fun u hu d hd => (H u hu d hd).trans_le h

theorem Visits.segment {M : Main.Machine} {input : List Bool} {c d : Config M}
    {time bound : ℕ} (H : Visits input c time bound)
    (result : runFrom (M.step input) c time = some d) :
    Segment (M.step input) (fun _ e => e.workHead < bound) c d time :=
  ⟨result, H⟩

theorem visits_of_envelope {M : Main.Machine} {input : List Bool} {c d : Config M}
    {time bound : ℕ} {E : Envelope} {F : Footprint} {base : Config M}
    (H : FirstExit (M.step input) (fun _ e => E.Contains e ∧ SameOutside F base e)
      {e | e.state = none} c d time) (hbound : E.workHi ≤ bound) :
    Visits input c time bound := by
  intro u hu e he
  exact ((H.during u hu e he).1.2.1).trans_le hbound

theorem visits_seq {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (a : Config A) (b : Config B) (s t bound : ℕ)
    (HA : FirstExit (A.step input) (fun _ _ => True) {d | d.state = none}
      (startOn A c) a s)
    (HB : FirstExit (B.step input) (fun _ _ => True) {d | d.state = none}
      (startOn B a) b t)
    (VA : Visits input (startOn A c) s bound) (VB : Visits input (startOn B a) t bound) :
    Visits input (startOn (Sequential.machine A B) c) (s + t) bound := by
  have H := Sequential.framed_compose A B input (I := fun _ d => d.workHead < bound)
    (VA.segment HA.result) (VB.segment HB.result)
    HA.exit_mem (fun u hu d hd => HA.cut u hu d hd)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  exact H.during

theorem visits_branch_true {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (a : Config A) (t bound : ℕ)
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (HA : FirstExit (A.step input) (fun _ _ => True) {d | d.state = none}
      (startOn A c) a t)
    (entry : c.workHead < bound) (VA : Visits input (startOn A c) t bound) :
    Visits input (startOn (Branch.machine A B) c) (1 + t) bound := by
  have H := Branch.framed_true A B input (startOn A c) a
    (I := fun _ d => d.workHead < bound) flag hi hc
    (VA.segment HA.result) entry (fun _ _ _ h => h)
  exact H.during

theorem visits_branch_false {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (b : Config B) (t bound : ℕ)
    (flag : c.work c.workHead = false)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (HB : FirstExit (B.step input) (fun _ _ => True) {d | d.state = none}
      (startOn B c) b t)
    (entry : c.workHead < bound) (VB : Visits input (startOn B c) t bound) :
    Visits input (startOn (Branch.machine A B) c) (1 + t) bound := by
  have H := Branch.framed_false A B input (startOn A c) b
    (I := fun _ d => d.workHead < bound) flag hi hc
    (VB.segment HB.result) entry (fun _ _ _ h => h)
  exact H.during

theorem visits_reentry {N : Main.Machine} (A : Main.Machine) (entry : Fin A.states)
    (input : List Bool) (c : Config N) (a : Config A) (t bound : ℕ)
    (HA : FirstExit (A.step input) (fun _ _ => True) {d | d.state = none}
      (enterOn A entry c) a t)
    (VA : Visits input (enterOn A entry c) t bound) :
    Visits input (startOn (Reentry.machine A entry) c) t bound := by
  have H := Reentry.framed A entry input (I := fun _ d => d.workHead < bound)
    (VA.segment HA.result) (fun _ _ _ h => h)
  exact H.during

theorem workBound_of_visits (M : Main.Machine) (input catalyst : List Bool) (time bound : ℕ)
    (H : Visits input (M.initial catalyst) time bound) : M.workBound input catalyst time bound := by
  intro u hu c hc
  apply H u hu c
  simpa only [runFrom_initial] using hc

end CatalyticTreeEval.Contracts.NativeRoundSupport
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeFrames -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeRoundSupport

/-- The native memory frame, allowing the two configurations to use different
finite-control types. The physical tapes keep their original meaning. -/
def Frame {A B : Main.Machine} (F : Footprint) (c : Config A) (d : Config B) : Prop :=
  (∀ p, p ∉ F.work → d.work p = c.work p) ∧
  d.catalyst.length = c.catalyst.length ∧
  (∀ p, p ∉ F.catalyst → d.catalyst[p]? = c.catalyst[p]?)

theorem Frame.refl {A : Main.Machine} (F : Footprint) (c : Config A) : Frame F c c :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩

theorem Frame.mono {A B : Main.Machine} {F G : Footprint} {c : Config A} {d : Config B}
    (H : Frame F c d) (hw : F.work ⊆ G.work) (hc : F.catalyst ⊆ G.catalyst) : Frame G c d :=
  ⟨fun p hp => H.1 p (fun h => hp (hw h)), H.2.1,
    fun p hp => H.2.2 p (fun h => hp (hc h))⟩

theorem Frame.trans {A B C : Main.Machine} {F : Footprint}
    {a : Config A} {b : Config B} {c : Config C} (H : Frame F a b) (K : Frame F b c) :
    Frame F a c :=
  ⟨fun p hp => (K.1 p hp).trans (H.1 p hp), K.2.1.trans H.2.1,
    fun p hp => (K.2.2 p hp).trans (H.2.2 p hp)⟩

def Frames {A B : Main.Machine} (input : List Bool) (base : Config A)
    (start : Config B) (time : ℕ) (F : Footprint) : Prop :=
  ∀ u ≤ time, ∀ d, runFrom (B.step input) start u = some d → Frame F base d

theorem Frames.mono {A B : Main.Machine} {input : List Bool} {base : Config A}
    {start : Config B} {time : ℕ} {F G : Footprint}
    (H : Frames input base start time F) (hw : F.work ⊆ G.work) (hc : F.catalyst ⊆ G.catalyst) :
    Frames input base start time G := fun u hu d hd => (H u hu d hd).mono hw hc

theorem frames_of_contract {M : Main.Machine} {input : List Bool} {c d base : Config M}
    {time : ℕ} {E : Envelope} {F : Footprint}
    (H : FirstExit (M.step input) (fun _ e => E.Contains e ∧ SameOutside F base e)
      {e | e.state = none} c d time) : Frames input base c time F :=
  fun u hu e he => (H.during u hu e he).2

theorem frames_seq {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (a : Config A) (b : Config B) (s t : ℕ) (F : Footprint)
    (HA : FirstExit (A.step input) (fun _ _ => True) {d | d.state = none}
      (startOn A c) a s)
    (HB : FirstExit (B.step input) (fun _ _ => True) {d | d.state = none}
      (startOn B a) b t)
    (FA : Frames input c (startOn A c) s F) (FB : Frames input a (startOn B a) t F) :
    Frames input c (startOn (Sequential.machine A B) c) (s + t) F := by
  have Fca := FA s le_rfl a HA.result
  have H := Sequential.framed_compose A B input
    (I := fun _ d => Frame F c d)
    (Segment.mk HA.result FA) (Segment.mk HB.result FB)
    HA.exit_mem (fun u hu d hd => HA.cut u hu d hd)
    (fun _ _ _ h => h) (fun _ _ _ h => Fca.trans h)
  exact H.during

theorem frames_branch_true {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (a : Config A) (t : ℕ) (F : Footprint)
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (HA : FirstExit (A.step input) (fun _ _ => True) {d | d.state = none}
      (startOn A c) a t)
    (FA : Frames input c (startOn A c) t F) :
    Frames input c (startOn (Branch.machine A B) c) (1 + t) F := by
  have H := Branch.framed_true A B input (startOn A c) a
    (I := fun _ d => Frame F c d) flag hi hc
    (Segment.mk HA.result FA) (Frame.refl F c) (fun _ _ _ h => h)
  exact H.during

theorem frames_branch_false {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (b : Config B) (t : ℕ) (F : Footprint)
    (flag : c.work c.workHead = false)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (HB : FirstExit (B.step input) (fun _ _ => True) {d | d.state = none}
      (startOn B c) b t)
    (FB : Frames input c (startOn B c) t F) :
    Frames input c (startOn (Branch.machine A B) c) (1 + t) F := by
  have H := Branch.framed_false A B input (startOn A c) b
    (I := fun _ d => Frame F c d) flag hi hc
    (Segment.mk HB.result FB) (Frame.refl F c) (fun _ _ _ h => h)
  exact H.during

theorem frames_reentry {N : Main.Machine} (A : Main.Machine) (entry : Fin A.states)
    (input : List Bool) (c : Config N) (a : Config A) (t : ℕ) (F : Footprint)
    (HA : FirstExit (A.step input) (fun _ _ => True) {d | d.state = none}
      (enterOn A entry c) a t)
    (FA : Frames input c (enterOn A entry c) t F) :
    Frames input c (startOn (Reentry.machine A entry) c) t F := by
  have H := Reentry.framed A entry input (I := fun _ d => Frame F c d)
    (Segment.mk HA.result FA) (fun _ _ _ h => h)
  exact H.during

end CatalyticTreeEval.Contracts.NativeRoundSupport
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeLiteral -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeLiteral

open CatalyticMatching.General

theorem position_le (direction : Move) (head u : ℕ) :
    position direction head u ≤ head + u := by
  induction u with
  | zero => simp [position]
  | succ u ih =>
    have hs : direction.apply (position direction head u) ≤ position direction head u + 1 := by
      cases direction <;> simp [Move.apply] <;> omega
    simp only [position]
    omega

theorem position_right (head u : ℕ) : position .right head u = head + u := by
  induction u with
  | zero => simp [position]
  | succ u ih => simp [position, Move.apply, ih, Nat.add_assoc]

theorem position_left (head u : ℕ) : position .left head u = head - u := by
  induction u with
  | zero => simp [position]
  | succ u ih => simp [position, Move.apply, ih, Nat.sub_sub]

theorem step_move (direction : Move) (moves : ℕ) (literal : Option Bool)
    (input : List Bool) (c : Config (machine direction moves literal)) (u : ℕ)
    (hu : u < moves) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    (machine direction moves literal).step input (live direction moves literal c u (by omega)) =
      some (live direction moves literal c (u + 1) (by omega)) := by
  simp [Machine.step, machine, live, hu, Move.apply, Function.update_eq_self,
    hi, hc, position]

theorem step_finish (direction : Move) (moves : ℕ) (literal : Option Bool)
    (input : List Bool) (c : Config (machine direction moves literal))
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    (machine direction moves literal).step input (live direction moves literal c moves le_rfl) =
      some (finished direction moves literal c) := by
  simp [Machine.step, machine, live, finished, Move.apply, hi, hc]

theorem run_live (direction : Move) (moves : ℕ) (literal : Option Bool)
    (input : List Bool) (c : Config (machine direction moves literal))
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    ∀ (u : ℕ) (hu : u ≤ moves),
      runFrom ((machine direction moves literal).step input)
        (live direction moves literal c 0 (by omega)) u =
        some (live direction moves literal c u hu) := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro hu
    rw [runFrom_succ, ih (by omega)]
    exact step_move direction moves literal input c u (by omega) hi hc

/-- Exact framed correctness of literal movement/writing, including its final
halting step and every addressed work cell along the trajectory. -/
theorem firstExit (direction : Move) (moves : ℕ) (literal : Option Bool)
    (input : List Bool) (c : Config (machine direction moves literal))
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    FirstExit ((machine direction moves literal).step input)
      (fun _ d =>
        (Envelope.mk 0 (c.workHead + moves + 1) c.catalystHead (c.catalystHead + 1)).Contains d ∧
        SameOutside (Footprint.mk {position direction c.workHead moves} ∅) c d)
      {d | d.state = none}
      (live direction moves literal c 0 (by omega)) (finished direction moves literal c)
      (moves + 1) where
  result := by
    rw [runFrom_succ, run_live direction moves literal input c hi hc moves le_rfl]
    exact step_finish direction moves literal input c hi hc
  during u hu d hd := by
    by_cases ht : u ≤ moves
    · rw [run_live direction moves literal input c hi hc u ht] at hd
      cases Option.some.inj hd
      have hp := position_le direction c.workHead u
      constructor
      · dsimp [Envelope.Contains, live]
        omega
      · simp [SameOutside, live]
    · have heq : u = moves + 1 := by omega
      subst u
      rw [runFrom_succ, run_live direction moves literal input c hi hc moves le_rfl] at hd
      simp only [Option.bind_some, step_finish direction moves literal input c hi hc] at hd
      cases Option.some.inj hd
      have hp := position_le direction c.workHead moves
      constructor
      · dsimp [Envelope.Contains, finished]
        omega
      · refine ⟨?_, rfl, fun _ _ => rfl⟩
        intro p hp
        exact Function.update_of_ne (by simpa using hp) _ _
  exit_mem := rfl
  cut u hu d hd := by
    rw [run_live direction moves literal input c hi hc u (by omega)] at hd
    cases Option.some.inj hd
    exact Option.some_ne_none _

end CatalyticTreeEval.Contracts.NativeLiteral
end

/- Proof source: Solutions.CatalyticTreeEvaluation.TaggedRewind -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.TaggedRewind

open CatalyticMatching.General

theorem step_leftCursor {toBank : Bool} (input : List Bool) (c : Config (machine toBank))
    (top u : ℕ) (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hu : u < top) (htag : 0 < u → u % 3 = 0 → c.work (top - u) = true) :
    (machine toBank).step input (leftCursor c top u) = some (leftCursor c top (u + 1)) := by
  have he : top - u - 1 = top - (u + 1) := by omega
  have hm := Nat.mod_lt u (by decide : 0 < 3)
  by_cases hz : u = 0
  · subst u
    simp [Machine.step, machine, instruction, leftCursor, cursor, Move.apply, hi, hc,
      Function.update_eq_self]
  · have hpos : 0 < u := by omega
    have hcases : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases hcases with h | h | h
    · have hs : (u + 1) % 3 = 1 := by omega
      have hread := htag hpos h
      simp [Machine.step, machine, instruction, leftCursor, cursor, Move.apply, hi, hc,
        hz, h, hs, he, hread, Function.update_eq_self]
    · have hs : (u + 1) % 3 = 2 := by omega
      simp [Machine.step, machine, instruction, leftCursor, cursor, Move.apply, hi, hc,
        hz, h, hs, he, Function.update_eq_self]
    · have hs : (u + 1) % 3 = 0 := by omega
      simp [Machine.step, machine, instruction, leftCursor, cursor, Move.apply, hi, hc,
        hz, h, hs, he, Function.update_eq_self]

theorem run_left {toBank : Bool} (input : List Bool) (c : Config (machine toBank))
    (base width : ℕ) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length)
    (htags : ∀ i < width, c.work (base + 6 + 3 * i) = true) :
    ∀ u ≤ 3 * width + 3,
      runFrom ((machine toBank).step input) (leftCursor c (base + 6 + 3 * width) 0) u =
        some (leftCursor c (base + 6 + 3 * width) u) := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
      intro hu
      rw [runFrom_succ, ih (by omega), Option.bind_some]
      apply step_leftCursor input c _ u hi hc (by omega)
      intro hup hum
      have he := Nat.mod_add_div u 3
      have hk : 0 < u / 3 ∧ u / 3 ≤ width := by omega
      have hidx : width - u / 3 < width := by omega
      have hhead : base + 6 + 3 * width - u = base + 6 + 3 * (width - u / 3) := by omega
      rw [hhead]
      exact htags _ hidx

theorem run_exit {toBank : Bool} (input : List Bool) (c : Config (machine toBank))
    (base : ℕ) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hmarker : c.work (base + 3) = false) :
    ∀ u ≤ 3,
      runFrom ((machine toBank).step input) (exitCursor c base 0) u = some (exitCursor c base u) := by
  have hself : Function.update c.work (base + 3) false = c.work := by
    rw [← hmarker]
    exact Function.update_eq_self _ _
  intro u hu
  have hcases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> cases toBank <;>
    simp [runFrom, Machine.step, machine, instruction, exitCursor, cursor, Move.apply,
      hi, hc, hmarker, hself, Function.update_eq_self]

theorem left_exit_seam {toBank : Bool} (c : Config (machine toBank)) (base width : ℕ) :
    leftCursor c (base + 6 + 3 * width) (3 * width + 3) = exitCursor c base 0 := by
  have hh : base + 6 + 3 * width - (3 * width + 3) = base + 3 := by omega
  have hz : ¬3 * width + 3 = 0 := by omega
  simp [leftCursor, exitCursor, hh, hz]

theorem run_prefix {toBank : Bool} (input : List Bool) (c : Config (machine toBank))
    (base width : ℕ) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hmarker : c.work (base + 3) = false)
    (htags : ∀ i < width, c.work (base + 6 + 3 * i) = true) (u : ℕ) (hu : u ≤ 3 * width + 6) :
    runFrom ((machine toBank).step input) (leftCursor c (base + 6 + 3 * width) 0) u =
      some (if u ≤ 3 * width + 3 then leftCursor c (base + 6 + 3 * width) u
        else exitCursor c base (u - (3 * width + 3))) := by
  by_cases h : u ≤ 3 * width + 3
  · simpa only [if_pos h] using run_left input c base width hi hc htags u h
  · rw [if_neg h]
    have he : u = (3 * width + 3) + (u - (3 * width + 3)) := by omega
    rw [he, runFrom_add, run_left input c base width hi hc htags _ le_rfl,
      Option.bind_some, left_exit_seam]
    have hrem : u - (3 * width + 3) ≤ 3 := by omega
    simpa only [Nat.add_sub_cancel_left] using run_exit input c base hi hc hmarker _ hrem

private theorem frame_cursor {toBank : Bool} (c : Config (machine toBank)) (base width head : ℕ)
    (q : Option (Fin 6)) (hlo : base ≤ head) (hhi : head ≤ base + 6 + 3 * width) :
    (envelope c base width).Contains (cursor c head q) ∧ SameOutside footprint c (cursor c head q) := by
  simp only [envelope, Envelope.Contains, cursor, SameOutside, footprint]
  exact ⟨by omega, by simp⟩

/-- The carry cell is never inspected as a tag and is preserved throughout.
The loop has no scratch footprint and charges every visited work position. -/
theorem firstExit {toBank : Bool} (input : List Bool) (c : Config (machine toBank))
    (base width : ℕ) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hmarker : c.work (base + 3) = false)
    (htags : ∀ i < width, c.work (base + 6 + 3 * i) = true) :
    FirstExit ((machine toBank).step input)
      (fun _ d => (envelope c base width).Contains d ∧ SameOutside footprint c d)
      {d | d.state = none}
      (leftCursor c (base + 6 + 3 * width) 0)
      (cursor c (if toBank then base + 6 else base) none) (3 * width + 6) where
  result := by
    have hrun := run_prefix input c base width hi hc hmarker htags (3 * width + 6) le_rfl
    simpa [show ¬3 * width + 6 ≤ 3 * width + 3 by omega, exitCursor] using hrun
  during u hu d hd := by
    rw [run_prefix input c base width hi hc hmarker htags u hu] at hd
    cases Option.some.inj hd
    split_ifs with h
    · apply frame_cursor <;> omega
    · unfold exitCursor
      apply frame_cursor <;> cases toBank <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  exit_mem := rfl
  cut u hu d hd := by
    rw [run_prefix input c base width hi hc hmarker htags u (by omega)] at hd
    cases Option.some.inj hd
    split_ifs with h
    · simp [leftCursor, cursor]
    · have hrem : u - (3 * width + 3) < 3 := by omega
      have hcases : u - (3 * width + 3) = 0 ∨ u - (3 * width + 3) = 1 ∨
          u - (3 * width + 3) = 2 := by omega
      rcases hcases with he | he | he <;> simp [exitCursor, cursor, he]


end CatalyticTreeEval.Contracts.TaggedRewind
end

/- Proof source: Solutions.CatalyticTreeEvaluation.RippleAdder -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RippleAdder

open CatalyticMatching.General

theorem fullAdder_value (carry a b : Bool) :
    (sumBit carry a b).toNat + 2 * (carryBit carry a b).toNat =
      carry.toNat + a.toNat + b.toNat := by
  cases carry <;> cases a <;> cases b <;> decide

theorem step_marker_true (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = true) :
    machine.step input (cursor c head (some (marker carry))) =
      some (cursor c (head + 1) (some (readA carry))) := by
  have hw : Function.update c.work head true = c.work := by
    simpa only [hm] using Function.update_eq_self head c.work
  cases carry <;>
    simp [Machine.step, machine, cursor, marker, markerInstruction, readA,
      Move.apply, hm, hw, hi, hc]

theorem step_readA (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (readA carry))) =
      some (cursor c (head + 1) (some (readB carry (c.work head)))) := by
  cases carry <;>
    simp [Machine.step, machine, cursor, readA, readAInstruction,
      Move.apply, Function.update_eq_self, hi, hc]

theorem step_readB (input : List Bool) (c : Config machine) (head : ℕ)
    (carry a : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (readB carry a))) =
      some (cursor c (head - 1)
        (some (writeA (carryBit carry a (c.work head)) (sumBit carry a (c.work head))))) := by
  cases carry <;> cases a <;>
    simp [Machine.step, machine, cursor, readB, readBInstruction,
      Move.apply, Function.update_eq_self, hi, hc]

theorem step_writeA (input : List Bool) (c : Config machine) (head : ℕ)
    (carry sum : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (writeA carry sum))) =
      some (cursor {c with work := Function.update c.work head sum} (head + 1)
        (some (skipB carry))) := by
  cases carry <;> cases sum <;>
    simp [Machine.step, machine, cursor, writeA, writeAInstruction,
      Move.apply, hi, hc]

theorem step_skipB (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (skipB carry))) =
      some (cursor c (head + 1) (some (marker carry))) := by
  cases carry <;>
    simp [Machine.step, machine, cursor, skipB, skipBInstruction,
      Move.apply, Function.update_eq_self, hi, hc]

theorem step_sentinel (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = false) :
    machine.step input (cursor c head (some (marker carry))) =
      some (cursor {c with work := Function.update c.work head carry} head none) := by
  cases carry <;>
    simp [Machine.step, machine, cursor, marker, markerInstruction,
      Move.apply, hm, hi, hc]

/-- A single column performs the full-adder truth table in exactly five native
transitions. The second operand and every other work cell are unchanged. -/
theorem run_column (input : List Bool) (c : Config machine) (head : ℕ)
    (carry a b : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = true)
    (ha : c.work (head + 1) = a) (hb : c.work (head + 2) = b) :
    runFrom (machine.step input) (cursor c head (some (marker carry))) 5 =
      some (cursor (writeSum c head (sumBit carry a b)) (head + 3)
        (some (marker (carryBit carry a b)))) := by
  simp only [runFrom, Option.bind_some]
  rw [step_marker_true input c head carry hi hc hm]
  simp only [Option.bind_some]
  rw [step_readA input c (head + 1) carry hi hc, ha]
  simp only [Option.bind_some]
  rw [step_readB input c (head + 1 + 1) carry a hi hc]
  simp only [show head + 1 + 1 = head + 2 by omega, hb,
    show head + 2 - 1 = head + 1 by omega, Option.bind_some]
  rw [step_writeA input c (head + 1) (carryBit carry a b) (sumBit carry a b) hi hc]
  simp only [Option.bind_some]
  rw [step_skipB]
  · rfl
  · exact hi
  · exact hc

/-- Every intermediate state of a column is live and lies in its four-cell
envelope. Only the first operand cell can change. -/
theorem column_segment (input : List Bool) (c : Config machine) (head : ℕ)
    (carry a b : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = true)
    (ha : c.work (head + 1) = a) (hb : c.work (head + 2) = b) :
    Segment (machine.step input)
      (fun _ d =>
        (Envelope.mk head (head + 4) c.catalystHead (c.catalystHead + 1)).Contains d ∧
        SameOutside (Footprint.mk {head + 1} ∅) c d ∧ d.state ≠ none)
      (cursor c head (some (marker carry)))
      (cursor (writeSum c head (sumBit carry a b)) (head + 3)
        (some (marker (carryBit carry a b)))) 5 where
  result := run_column input c head carry a b hi hc hm ha hb
  during u hu d hd := by
    have h0 := step_marker_true input c head carry hi hc hm
    have h1 : machine.step input (cursor c (head + 1) (some (readA carry))) =
        some (cursor c (head + 2) (some (readB carry a))) := by
      simpa only [ha, show head + 1 + 1 = head + 2 by omega] using
        step_readA input c (head + 1) carry hi hc
    have h2 : machine.step input (cursor c (head + 2) (some (readB carry a))) =
        some (cursor c (head + 1) (some (writeA (carryBit carry a b) (sumBit carry a b)))) := by
      simpa only [hb, show head + 2 - 1 = head + 1 by omega] using
        step_readB input c (head + 2) carry a hi hc
    have h3 : machine.step input
        (cursor c (head + 1) (some (writeA (carryBit carry a b) (sumBit carry a b)))) =
        some (cursor (writeSum c head (sumBit carry a b)) (head + 2)
          (some (skipB (carryBit carry a b)))) := by
      simpa only [writeSum, show head + 1 + 1 = head + 2 by omega] using
        step_writeA input c (head + 1) (carryBit carry a b) (sumBit carry a b) hi hc
    have h4 : machine.step input
        (cursor (writeSum c head (sumBit carry a b)) (head + 2)
          (some (skipB (carryBit carry a b)))) =
        some (cursor (writeSum c head (sumBit carry a b)) (head + 3)
          (some (marker (carryBit carry a b)))) := by
      exact step_skipB input (writeSum c head (sumBit carry a b)) (head + 2)
        (carryBit carry a b) hi hc
    interval_cases u <;>
      simp only [runFrom, h0, h1, h2, h3, h4, Option.bind_some] at hd <;>
      cases Option.some.inj hd <;>
      simp [Envelope.Contains, SameOutside, cursor, writeSum] <;>
      first | exact Option.some_ne_none _ | constructor
    all_goals first
      | exact Option.some_ne_none _
      | intro p hp; exact Function.update_of_ne hp _ _

end CatalyticTreeEval.Contracts.RippleAdder
end

/- Proof source: Solutions.CatalyticTreeEvaluation.RippleAdderBank -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RippleAdder

theorem prefixWork_marker (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed i : ℕ) :
    prefixWork work r a b initial processed (r + 3 * i) = work (r + 3 * i) := by
  simp [prefixWork, show (r + 3 * i - r) % 3 = 0 by omega]

theorem prefixWork_a (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed i : ℕ) :
    prefixWork work r a b initial processed (r + 3 * i + 1) =
      if i < processed then sumAt a b initial i else work (r + 3 * i + 1) := by
  simp [prefixWork, show r ≤ r + 3 * i + 1 by omega,
    show (r + 3 * i + 1 - r) % 3 = 1 by omega,
    show (r + 3 * i + 1 - r) / 3 = i by omega]

theorem prefixWork_b (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed i : ℕ) :
    prefixWork work r a b initial processed (r + 3 * i + 2) = work (r + 3 * i + 2) := by
  simp [prefixWork, show (r + 3 * i + 2 - r) % 3 = 2 by omega]

theorem prefixWork_zero (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool) (initial : Bool) :
    prefixWork work r a b initial 0 = work := by
  funext position
  simp [prefixWork]

theorem prefixWork_succ (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed : ℕ) :
    prefixWork work r a b initial (processed + 1) =
      Function.update (prefixWork work r a b initial processed)
        (r + 3 * processed + 1) (sumAt a b initial processed) := by
  funext position
  by_cases hp : position = r + 3 * processed + 1
  · subst position
    simp [prefixWork_a]
  · have hcond :
        (r ≤ position ∧ (position - r) % 3 = 1 ∧
          (position - r) / 3 < processed + 1) ↔
        (r ≤ position ∧ (position - r) % 3 = 1 ∧
          (position - r) / 3 < processed) := by
      constructor
      · rintro ⟨hr, hm, hn⟩
        refine ⟨hr, hm, ?_⟩
        have hdiv := Nat.mod_add_div (position - r) 3
        omega
      · omega
    rw [Function.update_of_ne hp]
    simp only [prefixWork, hcond]

theorem finished_sum (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (i : ℕ) (hi : i < width) :
    (finished c r width a b initial).work (r + 3 * i + 1) = sumAt a b initial i := by
  have hne : r + 3 * i + 1 ≠ r + 3 * width := by omega
  simp [finished, hne, prefixWork_a, hi]

theorem finished_preserves_b (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (i : ℕ) (hi : i < width) :
    (finished c r width a b initial).work (r + 3 * i + 2) = c.work (r + 3 * i + 2) := by
  have hne : r + 3 * i + 2 ≠ r + 3 * width := by omega
  simp [finished, hne, prefixWork_b]

theorem finished_carry (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) :
    (finished c r width a b initial).work (r + 3 * width) = carryAt a b initial width := by
  simp [finished]

/-- The truth table implies the usual arithmetic addition law for every width,
including the width-zero carry case. -/
theorem bankValue_add (a b : ℕ → Bool) (initial : Bool) (width : ℕ) :
    bankValue (sumAt a b initial) width +
        2 ^ width * (carryAt a b initial width).toNat =
      bankValue a width + bankValue b width + initial.toNat := by
  induction width with
  | zero => simp [bankValue, carryAt]
  | succ width ih =>
    have hf := fullAdder_value (carryAt a b initial width) (a width) (b width)
    have hfw := congrArg (fun n : ℕ => 2 ^ width * n) hf
    simp only [bankValue, Finset.sum_range_succ, carryAt, sumAt, pow_succ] at *
    nlinarith

/-- After the prescribed columns the machine has added the low bits and is at
the next column marker, with carry represented in finite control. -/
theorem run_columns (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    ∀ n ≤ width,
      runFrom (machine.step input) (cursor c r (some (marker initial))) (5 * n) =
        some (cursor {c with work := prefixWork c.work r a b initial n}
          (r + 3 * n) (some (marker (carryAt a b initial n)))) := by
  intro n
  induction n with
  | zero => intro _; simp [runFrom, prefixWork_zero, carryAt, cursor]
  | succ n ih =>
    intro hn
    rw [show 5 * (n + 1) = 5 * n + 5 by omega, runFrom_add, ih (by omega)]
    simp only [Option.bind_some]
    have hcol := run_column input {c with work := prefixWork c.work r a b initial n}
      (r + 3 * n) (carryAt a b initial n) (a n) (b n) hi hc
      (by simpa only [prefixWork_marker] using (hbank.2 n (by omega)).1)
      (by simpa only [prefixWork_a, lt_self_iff_false, ↓reduceIte] using
        (hbank.2 n (by omega)).2.1)
      (by simpa only [prefixWork_b] using (hbank.2 n (by omega)).2.2)
    simpa only [writeSum, sumAt, prefixWork_succ, carryAt,
      show r + 3 * n + 3 = r + 3 * (n + 1) by omega] using hcol

theorem run_bank (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    runFrom (machine.step input) (cursor c r (some (marker initial))) (5 * width + 1) =
      some (finished c r width a b initial) := by
  rw [runFrom_add, run_columns input c r width a b initial hi hc hbank width le_rfl]
  simp only [Option.bind_some, runFrom, Option.bind_some]
  rw [step_sentinel]
  · rfl
  · exact hi
  · exact hc
  · simpa only [prefixWork_marker] using hbank.1

theorem prefixWork_outside (work : ℕ → Bool) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed : ℕ) (hn : processed ≤ width) (position : ℕ)
    (hp : position ∉ Set.Ico r (r + 3 * width + 1)) :
    prefixWork work r a b initial processed position = work position := by
  have hnot : ¬(r ≤ position ∧ (position - r) % 3 = 1 ∧
      (position - r) / 3 < processed) := by
    rintro ⟨hr, hm, hdiv⟩
    have he := Nat.mod_add_div (position - r) 3
    apply hp
    constructor <;> omega
  simp only [prefixWork, if_neg hnot]

theorem prefix_frame (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed : ℕ) (hn : processed ≤ width) :
    SameOutside ⟨Set.Ico r (r + 3 * width + 1), ∅⟩ c
      {c with work := prefixWork c.work r a b initial processed} :=
  ⟨fun position hp => prefixWork_outside c.work r width a b initial processed hn position hp,
    rfl, fun _ _ => rfl⟩

/-- All columns execute within the whole bank, with an exact trajectory frame
and live finite control at every intermediate point. -/
theorem columns_segment (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    ∀ n ≤ width,
      Segment (machine.step input)
        (fun _ d =>
          (Envelope.mk r (r + 3 * width + 1) c.catalystHead (c.catalystHead + 1)).Contains d ∧
          SameOutside (Footprint.mk (Set.Ico r (r + 3 * width + 1)) ∅) c d ∧ d.state ≠ none)
        (cursor c r (some (marker initial)))
        (cursor {c with work := prefixWork c.work r a b initial n}
          (r + 3 * n) (some (marker (carryAt a b initial n)))) (5 * n) := by
  intro n
  induction n with
  | zero =>
    intro _
    constructor
    · simp [runFrom, prefixWork_zero, carryAt, cursor]
    · intro u hu d hd
      have hu0 : u = 0 := by omega
      subst u
      simp only [runFrom_zero] at hd
      cases Option.some.inj hd
      simp [Envelope.Contains, SameOutside, cursor]
      exact Option.some_ne_none _
  | succ n ih =>
    intro hn
    have hcol := column_segment input {c with work := prefixWork c.work r a b initial n}
      (r + 3 * n) (carryAt a b initial n) (a n) (b n) hi hc
      (by simpa only [prefixWork_marker] using (hbank.2 n (by omega)).1)
      (by simpa only [prefixWork_a, lt_self_iff_false, ↓reduceIte] using
        (hbank.2 n (by omega)).2.1)
      (by simpa only [prefixWork_b] using (hbank.2 n (by omega)).2.2)
    have H := (ih (by omega)).trans hcol (fun _ _ _ h => h) (fun _ _ _ h => by
      refine ⟨?_, ?_, h.2.2⟩
      · rcases h.1 with ⟨h1, h2, h3, h4⟩
        dsimp [Envelope.Contains] at *
        constructor
        · omega
        · constructor
          · omega
          · exact ⟨h3, h4⟩
      · have hF := (prefix_frame c r width a b initial n (by omega)).trans h.2.1
        apply hF.mono
        · intro position hp
          rcases hp with hp | hp
          · exact hp
          · have heq : position = r + 3 * n + 1 := Set.mem_singleton_iff.mp hp
            subst position
            constructor <;> omega
        · simp [Footprint.union])
    simpa only [writeSum, sumAt, prefixWork_succ, carryAt,
      show r + 3 * n + 3 = r + 3 * (n + 1) by omega,
      show 5 * n + 5 = 5 * (n + 1) by omega] using H

/-- The variable-width native addition leaf. It halts for the first time after
`5*width+1` transitions, at the carry cell. The charged work prefix ends at
`r+3*width+1`, which includes both any caller prefix and the final carry cell. -/
theorem bank_firstExit (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    FirstExit (machine.step input)
      (fun _ d =>
        (Envelope.mk r (r + 3 * width + 1) c.catalystHead (c.catalystHead + 1)).Contains d ∧
        SameOutside (Footprint.mk (Set.Ico r (r + 3 * width + 1)) ∅) c d)
      {d | d.state = none} (cursor c r (some (marker initial)))
      (finished c r width a b initial) (5 * width + 1) where
  result := run_bank input c r width a b initial hi hc hbank
  during u hu d hd := by
    by_cases ht : u ≤ 5 * width
    · have H := (columns_segment input c r width a b initial hi hc hbank width le_rfl).during
        u ht d hd
      exact ⟨H.1, H.2.1⟩
    · have heq : u = 5 * width + 1 := by omega
      subst u
      rw [run_bank input c r width a b initial hi hc hbank] at hd
      cases Option.some.inj hd
      constructor
      · simp [finished, Envelope.Contains]
      · refine ⟨?_, rfl, fun _ _ => rfl⟩
        intro position hp
        have hne : position ≠ r + 3 * width := by
          intro heq
          apply hp
          subst position
          constructor <;> omega
        simp only [finished, Function.update_of_ne hne]
        exact prefixWork_outside c.work r width a b initial width le_rfl position hp
  exit_mem := rfl
  cut u hu d hd := by
    exact ((columns_segment input c r width a b initial hi hc hbank width le_rfl).during
      u (by omega) d hd).2.2

end CatalyticTreeEval.Contracts.RippleAdder
end

/- Proof source: Solutions.CatalyticTreeEvaluation.RippleSubtractor -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RippleSubtractor

open CatalyticMatching.General

theorem fullAdder_value (carry a b : Bool) :
    (sumBit carry a b).toNat + 2 * (carryBit carry a b).toNat =
      carry.toNat + a.toNat + (!b).toNat := by
  cases carry <;> cases a <;> cases b <;> decide

theorem step_marker_true (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = true) :
    machine.step input (cursor c head (some (marker carry))) =
      some (cursor c (head + 1) (some (readA carry))) := by
  have hw : Function.update c.work head true = c.work := by
    simpa only [hm] using Function.update_eq_self head c.work
  cases carry <;>
    simp [Machine.step, machine, cursor, marker, markerInstruction, readA,
      Move.apply, hm, hw, hi, hc]

theorem step_readA (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (readA carry))) =
      some (cursor c (head + 1) (some (readB carry (c.work head)))) := by
  cases carry <;>
    simp [Machine.step, machine, cursor, readA, readAInstruction,
      Move.apply, Function.update_eq_self, hi, hc]

theorem step_readB (input : List Bool) (c : Config machine) (head : ℕ)
    (carry a : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (readB carry a))) =
      some (cursor c (head - 1)
        (some (writeA (carryBit carry a (c.work head)) (sumBit carry a (c.work head))))) := by
  cases carry <;> cases a <;>
    simp [Machine.step, machine, cursor, readB, readBInstruction,
      Move.apply, Function.update_eq_self, hi, hc]

theorem step_writeA (input : List Bool) (c : Config machine) (head : ℕ)
    (carry sum : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (writeA carry sum))) =
      some (cursor {c with work := Function.update c.work head sum} (head + 1)
        (some (skipB carry))) := by
  cases carry <;> cases sum <;>
    simp [Machine.step, machine, cursor, writeA, writeAInstruction,
      Move.apply, hi, hc]

theorem step_skipB (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (skipB carry))) =
      some (cursor c (head + 1) (some (marker carry))) := by
  cases carry <;>
    simp [Machine.step, machine, cursor, skipB, skipBInstruction,
      Move.apply, Function.update_eq_self, hi, hc]

theorem step_sentinel (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = false) :
    machine.step input (cursor c head (some (marker carry))) =
      some (cursor {c with work := Function.update c.work head carry} head none) := by
  cases carry <;>
    simp [Machine.step, machine, cursor, marker, markerInstruction,
      Move.apply, hm, hi, hc]

/-- A single column performs the full-adder truth table in exactly five native
transitions. The second operand and every other work cell are unchanged. -/
theorem run_column (input : List Bool) (c : Config machine) (head : ℕ)
    (carry a b : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = true)
    (ha : c.work (head + 1) = a) (hb : c.work (head + 2) = b) :
    runFrom (machine.step input) (cursor c head (some (marker carry))) 5 =
      some (cursor (writeSum c head (sumBit carry a b)) (head + 3)
        (some (marker (carryBit carry a b)))) := by
  simp only [runFrom, Option.bind_some]
  rw [step_marker_true input c head carry hi hc hm]
  simp only [Option.bind_some]
  rw [step_readA input c (head + 1) carry hi hc, ha]
  simp only [Option.bind_some]
  rw [step_readB input c (head + 1 + 1) carry a hi hc]
  simp only [show head + 1 + 1 = head + 2 by omega, hb,
    show head + 2 - 1 = head + 1 by omega, Option.bind_some]
  rw [step_writeA input c (head + 1) (carryBit carry a b) (sumBit carry a b) hi hc]
  simp only [Option.bind_some]
  rw [step_skipB]
  · rfl
  · exact hi
  · exact hc

/-- Every intermediate state of a column is live and lies in its four-cell
envelope. Only the first operand cell can change. -/
theorem column_segment (input : List Bool) (c : Config machine) (head : ℕ)
    (carry a b : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = true)
    (ha : c.work (head + 1) = a) (hb : c.work (head + 2) = b) :
    Segment (machine.step input)
      (fun _ d =>
        (Envelope.mk head (head + 4) c.catalystHead (c.catalystHead + 1)).Contains d ∧
        SameOutside (Footprint.mk {head + 1} ∅) c d ∧ d.state ≠ none)
      (cursor c head (some (marker carry)))
      (cursor (writeSum c head (sumBit carry a b)) (head + 3)
        (some (marker (carryBit carry a b)))) 5 where
  result := run_column input c head carry a b hi hc hm ha hb
  during u hu d hd := by
    have h0 := step_marker_true input c head carry hi hc hm
    have h1 : machine.step input (cursor c (head + 1) (some (readA carry))) =
        some (cursor c (head + 2) (some (readB carry a))) := by
      simpa only [ha, show head + 1 + 1 = head + 2 by omega] using
        step_readA input c (head + 1) carry hi hc
    have h2 : machine.step input (cursor c (head + 2) (some (readB carry a))) =
        some (cursor c (head + 1) (some (writeA (carryBit carry a b) (sumBit carry a b)))) := by
      simpa only [hb, show head + 2 - 1 = head + 1 by omega] using
        step_readB input c (head + 2) carry a hi hc
    have h3 : machine.step input
        (cursor c (head + 1) (some (writeA (carryBit carry a b) (sumBit carry a b)))) =
        some (cursor (writeSum c head (sumBit carry a b)) (head + 2)
          (some (skipB (carryBit carry a b)))) := by
      simpa only [writeSum, show head + 1 + 1 = head + 2 by omega] using
        step_writeA input c (head + 1) (carryBit carry a b) (sumBit carry a b) hi hc
    have h4 : machine.step input
        (cursor (writeSum c head (sumBit carry a b)) (head + 2)
          (some (skipB (carryBit carry a b)))) =
        some (cursor (writeSum c head (sumBit carry a b)) (head + 3)
          (some (marker (carryBit carry a b)))) := by
      exact step_skipB input (writeSum c head (sumBit carry a b)) (head + 2)
        (carryBit carry a b) hi hc
    interval_cases u <;>
      simp only [runFrom, h0, h1, h2, h3, h4, Option.bind_some] at hd <;>
      cases Option.some.inj hd <;>
      simp [Envelope.Contains, SameOutside, cursor, writeSum] <;>
      first | exact Option.some_ne_none _ | constructor
    all_goals first
      | exact Option.some_ne_none _
      | intro p hp; exact Function.update_of_ne hp _ _

end CatalyticTreeEval.Contracts.RippleSubtractor
end

/- Proof source: Solutions.CatalyticTreeEvaluation.RippleSubtractorBank -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RippleSubtractor

theorem prefixWork_marker (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed i : ℕ) :
    prefixWork work r a b initial processed (r + 3 * i) = work (r + 3 * i) := by
  simp [prefixWork, show (r + 3 * i - r) % 3 = 0 by omega]

theorem prefixWork_a (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed i : ℕ) :
    prefixWork work r a b initial processed (r + 3 * i + 1) =
      if i < processed then sumAt a b initial i else work (r + 3 * i + 1) := by
  simp [prefixWork, show r ≤ r + 3 * i + 1 by omega,
    show (r + 3 * i + 1 - r) % 3 = 1 by omega,
    show (r + 3 * i + 1 - r) / 3 = i by omega]

theorem prefixWork_b (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed i : ℕ) :
    prefixWork work r a b initial processed (r + 3 * i + 2) = work (r + 3 * i + 2) := by
  simp [prefixWork, show (r + 3 * i + 2 - r) % 3 = 2 by omega]

theorem prefixWork_zero (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool) (initial : Bool) :
    prefixWork work r a b initial 0 = work := by
  funext position
  simp [prefixWork]

theorem prefixWork_succ (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed : ℕ) :
    prefixWork work r a b initial (processed + 1) =
      Function.update (prefixWork work r a b initial processed)
        (r + 3 * processed + 1) (sumAt a b initial processed) := by
  funext position
  by_cases hp : position = r + 3 * processed + 1
  · subst position
    simp [prefixWork_a]
  · have hcond :
        (r ≤ position ∧ (position - r) % 3 = 1 ∧
          (position - r) / 3 < processed + 1) ↔
        (r ≤ position ∧ (position - r) % 3 = 1 ∧
          (position - r) / 3 < processed) := by
      constructor
      · rintro ⟨hr, hm, hn⟩
        refine ⟨hr, hm, ?_⟩
        have hdiv := Nat.mod_add_div (position - r) 3
        omega
      · omega
    rw [Function.update_of_ne hp]
    simp only [prefixWork, hcond]

theorem finished_sum (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (i : ℕ) (hi : i < width) :
    (finished c r width a b initial).work (r + 3 * i + 1) = sumAt a b initial i := by
  have hne : r + 3 * i + 1 ≠ r + 3 * width := by omega
  simp [finished, hne, prefixWork_a, hi]

theorem finished_preserves_b (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (i : ℕ) (hi : i < width) :
    (finished c r width a b initial).work (r + 3 * i + 2) = c.work (r + 3 * i + 2) := by
  have hne : r + 3 * i + 2 ≠ r + 3 * width := by omega
  simp [finished, hne, prefixWork_b]

theorem finished_carry (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) :
    (finished c r width a b initial).work (r + 3 * width) = carryAt a b initial width := by
  simp [finished]

theorem carryAt_complement (a b : ℕ → Bool) (initial : Bool) (n : ℕ) :
    carryAt a b initial n = RippleAdder.carryAt a (fun i => !b i) initial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [carryAt, RippleAdder.carryAt, ih]; rfl

theorem sumAt_complement (a b : ℕ → Bool) (initial : Bool) (n : ℕ) :
    sumAt a b initial n = RippleAdder.sumAt a (fun i => !b i) initial n := by
  simp only [sumAt, RippleAdder.sumAt, carryAt_complement]
  rfl

theorem bankValue_complement (b : ℕ → Bool) (width : ℕ) :
    bankValue (fun i => !b i) width + bankValue b width + 1 = 2 ^ width := by
  induction width with
  | zero => simp [bankValue]
  | succ width ih =>
    have hbit : (!b width).toNat + (b width).toNat = 1 := by cases b width <;> decide
    have hbitw := congrArg (fun n : ℕ => 2 ^ width * n) hbit
    simp only [bankValue, Finset.sum_range_succ, pow_succ] at *
    nlinarith

theorem bankValue_subtract (a b : ℕ → Bool) (width : ℕ) :
    bankValue (sumAt a b true) width +
        2 ^ width * (carryAt a b true width).toNat + bankValue b width =
      bankValue a width + 2 ^ width := by
  have h := RippleAdder.bankValue_add a (fun i => !b i) true width
  have hc := bankValue_complement b width
  have hs : (fun i => sumAt a b true i) = RippleAdder.sumAt a (fun i => !b i) true :=
    funext (sumAt_complement a b true)
  rw [← hs, ← carryAt_complement] at h
  change bankValue (sumAt a b true) width +
    2 ^ width * (carryAt a b true width).toNat =
    bankValue a width + bankValue (fun i => !b i) width + 1 at h
  omega

theorem bankValue_lt (bits : ℕ → Bool) (width : ℕ) : bankValue bits width < 2 ^ width := by
  induction width with
  | zero => simp [bankValue]
  | succ width ih =>
    have hb : (bits width).toNat ≤ 1 := by cases bits width <;> decide
    have hp : 0 < 2 ^ width := Nat.two_pow_pos width
    have hbw := Nat.mul_le_mul_right (2 ^ width) hb
    simp only [bankValue, Finset.sum_range_succ, pow_succ] at *
    nlinarith

/-- A true final carry is precisely the comparison `B ≤ A`. -/
theorem carryAt_subtract_iff (a b : ℕ → Bool) (width : ℕ) :
    carryAt a b true width = true ↔ bankValue b width ≤ bankValue a width := by
  have h := bankValue_subtract a b width
  have hs := bankValue_lt (sumAt a b true) width
  constructor
  · intro hc
    rw [hc] at h
    simp only [Bool.toNat_true, mul_one] at h
    omega
  · intro hle
    cases hc : carryAt a b true width with
    | false =>
      rw [hc] at h
      simp only [Bool.toNat_false, mul_zero, add_zero] at h
      omega
    | true => rfl

/-- After the prescribed columns the machine has added the low bits and is at
the next column marker, with carry represented in finite control. -/
theorem run_columns (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    ∀ n ≤ width,
      runFrom (machine.step input) (cursor c r (some (marker initial))) (5 * n) =
        some (cursor {c with work := prefixWork c.work r a b initial n}
          (r + 3 * n) (some (marker (carryAt a b initial n)))) := by
  intro n
  induction n with
  | zero => intro _; simp [runFrom, prefixWork_zero, carryAt, cursor]
  | succ n ih =>
    intro hn
    rw [show 5 * (n + 1) = 5 * n + 5 by omega, runFrom_add, ih (by omega)]
    simp only [Option.bind_some]
    have hcol := run_column input {c with work := prefixWork c.work r a b initial n}
      (r + 3 * n) (carryAt a b initial n) (a n) (b n) hi hc
      (by simpa only [prefixWork_marker] using (hbank.2 n (by omega)).1)
      (by simpa only [prefixWork_a, lt_self_iff_false, ↓reduceIte] using
        (hbank.2 n (by omega)).2.1)
      (by simpa only [prefixWork_b] using (hbank.2 n (by omega)).2.2)
    simpa only [writeSum, sumAt, prefixWork_succ, carryAt,
      show r + 3 * n + 3 = r + 3 * (n + 1) by omega] using hcol

theorem run_bank (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    runFrom (machine.step input) (cursor c r (some (marker initial))) (5 * width + 1) =
      some (finished c r width a b initial) := by
  rw [runFrom_add, run_columns input c r width a b initial hi hc hbank width le_rfl]
  simp only [Option.bind_some, runFrom, Option.bind_some]
  rw [step_sentinel]
  · rfl
  · exact hi
  · exact hc
  · simpa only [prefixWork_marker] using hbank.1

theorem prefixWork_outside (work : ℕ → Bool) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed : ℕ) (hn : processed ≤ width) (position : ℕ)
    (hp : position ∉ Set.Ico r (r + 3 * width + 1)) :
    prefixWork work r a b initial processed position = work position := by
  have hnot : ¬(r ≤ position ∧ (position - r) % 3 = 1 ∧
      (position - r) / 3 < processed) := by
    rintro ⟨hr, hm, hdiv⟩
    have he := Nat.mod_add_div (position - r) 3
    apply hp
    constructor <;> omega
  simp only [prefixWork, if_neg hnot]

theorem prefix_frame (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed : ℕ) (hn : processed ≤ width) :
    SameOutside ⟨Set.Ico r (r + 3 * width + 1), ∅⟩ c
      {c with work := prefixWork c.work r a b initial processed} :=
  ⟨fun position hp => prefixWork_outside c.work r width a b initial processed hn position hp,
    rfl, fun _ _ => rfl⟩

/-- All columns execute within the whole bank, with an exact trajectory frame
and live finite control at every intermediate point. -/
theorem columns_segment (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    ∀ n ≤ width,
      Segment (machine.step input)
        (fun _ d =>
          (Envelope.mk r (r + 3 * width + 1) c.catalystHead (c.catalystHead + 1)).Contains d ∧
          SameOutside (Footprint.mk (Set.Ico r (r + 3 * width + 1)) ∅) c d ∧ d.state ≠ none)
        (cursor c r (some (marker initial)))
        (cursor {c with work := prefixWork c.work r a b initial n}
          (r + 3 * n) (some (marker (carryAt a b initial n)))) (5 * n) := by
  intro n
  induction n with
  | zero =>
    intro _
    constructor
    · simp [runFrom, prefixWork_zero, carryAt, cursor]
    · intro u hu d hd
      have hu0 : u = 0 := by omega
      subst u
      simp only [runFrom_zero] at hd
      cases Option.some.inj hd
      simp [Envelope.Contains, SameOutside, cursor]
      exact Option.some_ne_none _
  | succ n ih =>
    intro hn
    have hcol := column_segment input {c with work := prefixWork c.work r a b initial n}
      (r + 3 * n) (carryAt a b initial n) (a n) (b n) hi hc
      (by simpa only [prefixWork_marker] using (hbank.2 n (by omega)).1)
      (by simpa only [prefixWork_a, lt_self_iff_false, ↓reduceIte] using
        (hbank.2 n (by omega)).2.1)
      (by simpa only [prefixWork_b] using (hbank.2 n (by omega)).2.2)
    have H := (ih (by omega)).trans hcol (fun _ _ _ h => h) (fun _ _ _ h => by
      refine ⟨?_, ?_, h.2.2⟩
      · rcases h.1 with ⟨h1, h2, h3, h4⟩
        dsimp [Envelope.Contains] at *
        constructor
        · omega
        · constructor
          · omega
          · exact ⟨h3, h4⟩
      · have hF := (prefix_frame c r width a b initial n (by omega)).trans h.2.1
        apply hF.mono
        · intro position hp
          rcases hp with hp | hp
          · exact hp
          · have heq : position = r + 3 * n + 1 := Set.mem_singleton_iff.mp hp
            subst position
            constructor <;> omega
        · simp [Footprint.union])
    simpa only [writeSum, sumAt, prefixWork_succ, carryAt,
      show r + 3 * n + 3 = r + 3 * (n + 1) by omega,
      show 5 * n + 5 = 5 * (n + 1) by omega] using H

/-- The variable-width native subtraction leaf. It halts for the first time after
`5*width+1` transitions, at the carry cell. The charged work prefix ends at
`r+3*width+1`, which includes both any caller prefix and the final carry cell. -/
theorem bank_firstExit (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    FirstExit (machine.step input)
      (fun _ d =>
        (Envelope.mk r (r + 3 * width + 1) c.catalystHead (c.catalystHead + 1)).Contains d ∧
        SameOutside (Footprint.mk (Set.Ico r (r + 3 * width + 1)) ∅) c d)
      {d | d.state = none} (cursor c r (some (marker initial)))
      (finished c r width a b initial) (5 * width + 1) where
  result := run_bank input c r width a b initial hi hc hbank
  during u hu d hd := by
    by_cases ht : u ≤ 5 * width
    · have H := (columns_segment input c r width a b initial hi hc hbank width le_rfl).during
        u ht d hd
      exact ⟨H.1, H.2.1⟩
    · have heq : u = 5 * width + 1 := by omega
      subst u
      rw [run_bank input c r width a b initial hi hc hbank] at hd
      cases Option.some.inj hd
      constructor
      · simp [finished, Envelope.Contains]
      · refine ⟨?_, rfl, fun _ _ => rfl⟩
        intro position hp
        have hne : position ≠ r + 3 * width := by
          intro heq
          apply hp
          subst position
          constructor <;> omega
        simp only [finished, Function.update_of_ne hne]
        exact prefixWork_outside c.work r width a b initial width le_rfl position hp
  exit_mem := rfl
  cut u hu d hd := by
    exact ((columns_segment input c r width a b initial hi hc hbank width le_rfl).during
      u (by omega) d hd).2.2

end CatalyticTreeEval.Contracts.RippleSubtractor
end

/- Proof source: Solutions.CatalyticTreeEvaluation.ShiftAppend -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.ShiftAppend

open CatalyticMatching.General

theorem fullAdder_value (carry a b : Bool) :
    (sumBit carry a b).toNat + 2 * (carryBit carry a b).toNat =
      carry.toNat + 2 * a.toNat := rfl

theorem step_marker_true (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = true) :
    machine.step input (cursor c head (some (marker carry))) =
      some (cursor c (head + 1) (some (writeA carry))) := by
  have hw : Function.update c.work head true = c.work := by
    simpa only [hm] using Function.update_eq_self head c.work
  cases carry <;>
    simp [CatalyticMatching.General.Machine.step, machine, cursor, marker,
      markerInstruction, writeA, Move.apply, hm, hw, hi, hc]

theorem step_writeA (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (writeA carry))) =
      some (cursor {c with work := Function.update c.work head carry} (head + 1)
        (some (skipB (c.work head)))) := by
  cases carry <;>
    simp [CatalyticMatching.General.Machine.step, machine, cursor, writeA,
      writeAInstruction, Move.apply, hi, hc]

theorem step_skipB (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    machine.step input (cursor c head (some (skipB carry))) =
      some (cursor c (head + 1) (some (marker carry))) := by
  cases carry <;>
    simp [CatalyticMatching.General.Machine.step, machine, cursor, skipB,
      skipBInstruction, Move.apply, Function.update_eq_self, hi, hc]

theorem step_sentinel (input : List Bool) (c : Config machine) (head : ℕ)
    (carry : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = false) :
    machine.step input (cursor c head (some (marker carry))) =
      some (cursor {c with work := Function.update c.work head carry} head none) := by
  cases carry <;>
    simp [CatalyticMatching.General.Machine.step, machine, cursor, marker,
      markerInstruction, Move.apply, hm, hi, hc]

theorem run_column (input : List Bool) (c : Config machine) (head : ℕ)
    (carry a b : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = true)
    (ha : c.work (head + 1) = a) (_hb : c.work (head + 2) = b) :
    runFrom (machine.step input) (cursor c head (some (marker carry))) 3 =
      some (cursor (writeSum c head (sumBit carry a b)) (head + 3)
        (some (marker (carryBit carry a b)))) := by
  simp only [runFrom, Option.bind_some]
  rw [step_marker_true input c head carry hi hc hm]
  simp only [Option.bind_some]
  rw [step_writeA input c (head + 1) carry hi hc, ha]
  simp only [Option.bind_some]
  rw [step_skipB]
  · rfl
  · exact hi
  · exact hc

theorem column_segment (input : List Bool) (c : Config machine) (head : ℕ)
    (carry a b : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hm : c.work head = true)
    (ha : c.work (head + 1) = a) (hb : c.work (head + 2) = b) :
    Segment (machine.step input)
      (fun _ d =>
        (Envelope.mk head (head + 4) c.catalystHead (c.catalystHead + 1)).Contains d ∧
        SameOutside (Footprint.mk {head + 1} ∅) c d ∧ d.state ≠ none)
      (cursor c head (some (marker carry)))
      (cursor (writeSum c head (sumBit carry a b)) (head + 3)
        (some (marker (carryBit carry a b)))) 3 where
  result := run_column input c head carry a b hi hc hm ha hb
  during u hu d hd := by
    have h0 := step_marker_true input c head carry hi hc hm
    have h1 : machine.step input (cursor c (head + 1) (some (writeA carry))) =
        some (cursor (writeSum c head carry) (head + 2) (some (skipB a))) := by
      simpa only [ha, writeSum, show head + 1 + 1 = head + 2 by omega] using
        step_writeA input c (head + 1) carry hi hc
    have h2 : machine.step input (cursor (writeSum c head carry) (head + 2) (some (skipB a))) =
        some (cursor (writeSum c head carry) (head + 3) (some (marker a))) := by
      exact step_skipB input (writeSum c head carry) (head + 2) a hi hc
    interval_cases u <;>
      simp only [runFrom, h0, h1, h2, Option.bind_some] at hd <;>
      cases Option.some.inj hd <;>
      simp [Envelope.Contains, SameOutside, cursor, writeSum] <;>
      first | exact Option.some_ne_none _ | constructor
    all_goals first
      | exact Option.some_ne_none _
      | intro p hp; exact Function.update_of_ne hp _ _

end CatalyticTreeEval.Contracts.ShiftAppend
end

/- Proof source: Solutions.CatalyticTreeEvaluation.ShiftAppendBank -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.ShiftAppend

theorem prefixWork_marker (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed i : ℕ) :
    prefixWork work r a b initial processed (r + 3 * i) = work (r + 3 * i) := by
  simp [prefixWork, show (r + 3 * i - r) % 3 = 0 by omega]

theorem prefixWork_a (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed i : ℕ) :
    prefixWork work r a b initial processed (r + 3 * i + 1) =
      if i < processed then sumAt a b initial i else work (r + 3 * i + 1) := by
  simp [prefixWork, show r ≤ r + 3 * i + 1 by omega,
    show (r + 3 * i + 1 - r) % 3 = 1 by omega,
    show (r + 3 * i + 1 - r) / 3 = i by omega]

theorem prefixWork_b (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed i : ℕ) :
    prefixWork work r a b initial processed (r + 3 * i + 2) = work (r + 3 * i + 2) := by
  simp [prefixWork, show (r + 3 * i + 2 - r) % 3 = 2 by omega]

theorem prefixWork_zero (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool) (initial : Bool) :
    prefixWork work r a b initial 0 = work := by
  funext position
  simp [prefixWork]

theorem prefixWork_succ (work : ℕ → Bool) (r : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed : ℕ) :
    prefixWork work r a b initial (processed + 1) =
      Function.update (prefixWork work r a b initial processed)
        (r + 3 * processed + 1) (sumAt a b initial processed) := by
  funext position
  by_cases hp : position = r + 3 * processed + 1
  · subst position
    simp [prefixWork_a]
  · have hcond :
        (r ≤ position ∧ (position - r) % 3 = 1 ∧
          (position - r) / 3 < processed + 1) ↔
        (r ≤ position ∧ (position - r) % 3 = 1 ∧
          (position - r) / 3 < processed) := by
      constructor
      · rintro ⟨hr, hm, hn⟩
        refine ⟨hr, hm, ?_⟩
        have hdiv := Nat.mod_add_div (position - r) 3
        omega
      · omega
    rw [Function.update_of_ne hp]
    simp only [prefixWork, hcond]

theorem finished_sum (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (i : ℕ) (hi : i < width) :
    (finished c r width a b initial).work (r + 3 * i + 1) = sumAt a b initial i := by
  have hne : r + 3 * i + 1 ≠ r + 3 * width := by omega
  simp [finished, hne, prefixWork_a, hi]

theorem finished_preserves_b (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (i : ℕ) (hi : i < width) :
    (finished c r width a b initial).work (r + 3 * i + 2) = c.work (r + 3 * i + 2) := by
  have hne : r + 3 * i + 2 ≠ r + 3 * width := by omega
  simp [finished, hne, prefixWork_b]

theorem finished_carry (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) :
    (finished c r width a b initial).work (r + 3 * width) = carryAt a b initial width := by
  simp [finished]

/-- A left shift with appended input bit is multiplication by two plus that bit. -/
theorem bankValue_append (a b : ℕ → Bool) (initial : Bool) (width : ℕ) :
    bankValue (sumAt a b initial) width +
        2 ^ width * (carryAt a b initial width).toNat =
      2 * bankValue a width + initial.toNat := by
  induction width with
  | zero => simp [bankValue, carryAt]
  | succ width ih =>
    have hf := fullAdder_value (carryAt a b initial width) (a width) (b width)
    have hfw := congrArg (fun n : ℕ => 2 ^ width * n) hf
    simp only [bankValue, Finset.sum_range_succ, carryAt, sumAt, pow_succ] at *
    nlinarith

/-- After the prescribed columns the machine has added the low bits and is at
the next column marker, with carry represented in finite control. -/
theorem run_columns (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    ∀ n ≤ width,
      runFrom (machine.step input) (cursor c r (some (marker initial))) (3 * n) =
        some (cursor {c with work := prefixWork c.work r a b initial n}
          (r + 3 * n) (some (marker (carryAt a b initial n)))) := by
  intro n
  induction n with
  | zero => intro _; simp [runFrom, prefixWork_zero, carryAt, cursor]
  | succ n ih =>
    intro hn
    rw [show 3 * (n + 1) = 3 * n + 3 by omega, runFrom_add, ih (by omega)]
    simp only [Option.bind_some]
    have hcol := run_column input {c with work := prefixWork c.work r a b initial n}
      (r + 3 * n) (carryAt a b initial n) (a n) (b n) hi hc
      (by simpa only [prefixWork_marker] using (hbank.2 n (by omega)).1)
      (by simpa only [prefixWork_a, lt_self_iff_false, ↓reduceIte] using
        (hbank.2 n (by omega)).2.1)
      (by simpa only [prefixWork_b] using (hbank.2 n (by omega)).2.2)
    simpa only [writeSum, sumAt, prefixWork_succ, carryAt, Nat.add_assoc,
      Nat.mul_add, Nat.mul_one] using hcol

theorem run_bank (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    runFrom (machine.step input) (cursor c r (some (marker initial))) (3 * width + 1) =
      some (finished c r width a b initial) := by
  rw [runFrom_add, run_columns input c r width a b initial hi hc hbank width le_rfl]
  simp only [Option.bind_some, runFrom, Option.bind_some]
  rw [step_sentinel]
  · rfl
  · exact hi
  · exact hc
  · simpa only [prefixWork_marker] using hbank.1

theorem prefixWork_outside (work : ℕ → Bool) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed : ℕ) (hn : processed ≤ width) (position : ℕ)
    (hp : position ∉ Set.Ico r (r + 3 * width + 1)) :
    prefixWork work r a b initial processed position = work position := by
  have hnot : ¬(r ≤ position ∧ (position - r) % 3 = 1 ∧
      (position - r) / 3 < processed) := by
    rintro ⟨hr, hm, hdiv⟩
    have he := Nat.mod_add_div (position - r) 3
    apply hp
    constructor <;> omega
  simp only [prefixWork, if_neg hnot]

theorem prefix_frame (c : Config machine) (r width : ℕ) (a b : ℕ → Bool)
    (initial : Bool) (processed : ℕ) (hn : processed ≤ width) :
    SameOutside ⟨Set.Ico r (r + 3 * width + 1), ∅⟩ c
      {c with work := prefixWork c.work r a b initial processed} :=
  ⟨fun position hp => prefixWork_outside c.work r width a b initial processed hn position hp,
    rfl, fun _ _ => rfl⟩

/-- All columns execute within the whole bank, with an exact trajectory frame
and live finite control at every intermediate point. -/
theorem columns_segment (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    ∀ n ≤ width,
      Segment (machine.step input)
        (fun _ d =>
          (Envelope.mk r (r + 3 * width + 1) c.catalystHead (c.catalystHead + 1)).Contains d ∧
          SameOutside (Footprint.mk (Set.Ico r (r + 3 * width + 1)) ∅) c d ∧ d.state ≠ none)
        (cursor c r (some (marker initial)))
        (cursor {c with work := prefixWork c.work r a b initial n}
          (r + 3 * n) (some (marker (carryAt a b initial n)))) (3 * n) := by
  intro n
  induction n with
  | zero =>
    intro _
    constructor
    · simp [runFrom, prefixWork_zero, carryAt, cursor]
    · intro u hu d hd
      have hu0 : u = 0 := by omega
      subst u
      simp only [runFrom_zero] at hd
      cases Option.some.inj hd
      simp [Envelope.Contains, SameOutside, cursor]
      exact Option.some_ne_none _
  | succ n ih =>
    intro hn
    have hcol := column_segment input {c with work := prefixWork c.work r a b initial n}
      (r + 3 * n) (carryAt a b initial n) (a n) (b n) hi hc
      (by simpa only [prefixWork_marker] using (hbank.2 n (by omega)).1)
      (by simpa only [prefixWork_a, lt_self_iff_false, ↓reduceIte] using
        (hbank.2 n (by omega)).2.1)
      (by simpa only [prefixWork_b] using (hbank.2 n (by omega)).2.2)
    have H := (ih (by omega)).trans hcol (fun _ _ _ h => h) (fun _ _ _ h => by
      refine ⟨?_, ?_, h.2.2⟩
      · rcases h.1 with ⟨h1, h2, h3, h4⟩
        dsimp [Envelope.Contains] at *
        constructor
        · omega
        · constructor
          · omega
          · exact ⟨h3, h4⟩
      · have hF := (prefix_frame c r width a b initial n (by omega)).trans h.2.1
        apply hF.mono
        · intro position hp
          rcases hp with hp | hp
          · exact hp
          · have heq : position = r + 3 * n + 1 := Set.mem_singleton_iff.mp hp
            subst position
            constructor <;> omega
        · simp [Footprint.union])
    simpa only [writeSum, sumAt, prefixWork_succ, carryAt, Nat.add_assoc,
      Nat.mul_add, Nat.mul_one] using H

/-- The variable-width native left shift leaf. It halts for the first time after
`3*width+1` transitions, at the carry cell. The charged work prefix ends at
`r+3*width+1`, which includes both any caller prefix and the final carry cell. -/
theorem bank_firstExit (input : List Bool) (c : Config machine) (r width : ℕ)
    (a b : ℕ → Bool) (initial : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work r width a b) :
    FirstExit (machine.step input)
      (fun _ d =>
        (Envelope.mk r (r + 3 * width + 1) c.catalystHead (c.catalystHead + 1)).Contains d ∧
        SameOutside (Footprint.mk (Set.Ico r (r + 3 * width + 1)) ∅) c d)
      {d | d.state = none} (cursor c r (some (marker initial)))
      (finished c r width a b initial) (3 * width + 1) where
  result := run_bank input c r width a b initial hi hc hbank
  during u hu d hd := by
    by_cases ht : u ≤ 3 * width
    · have H := (columns_segment input c r width a b initial hi hc hbank width le_rfl).during
        u ht d hd
      exact ⟨H.1, H.2.1⟩
    · have heq : u = 3 * width + 1 := by omega
      subst u
      rw [run_bank input c r width a b initial hi hc hbank] at hd
      cases Option.some.inj hd
      constructor
      · simp [finished, Envelope.Contains]
      · refine ⟨?_, rfl, fun _ _ => rfl⟩
        intro position hp
        have hne : position ≠ r + 3 * width := by
          intro heq
          apply hp
          subst position
          constructor <;> omega
        simp only [finished, Function.update_of_ne hne]
        exact prefixWork_outside c.work r width a b initial width le_rfl position hp
  exit_mem := rfl
  cut u hu d hd := by
    exact ((columns_segment input c r width a b initial hi hc hbank width le_rfl).during
      u (by omega) d hd).2.2

end CatalyticTreeEval.Contracts.ShiftAppend
end

/- Proof source: Solutions.CatalyticTreeEvaluation.RestoringDivision -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.BinaryArithmetic

theorem divisionStep_decomposition (m : ℕ) (s : DivisionState) (bit : Bool) :
    (divisionStep m s bit).quotient * m + (divisionStep m s bit).remainder =
      2 * (s.quotient * m + s.remainder) + bit.toNat := by
  by_cases h : m ≤ 2 * s.remainder + bit.toNat
  · have hs := Nat.sub_add_cancel h
    simp only [divisionStep, if_pos h]
    nlinarith
  · simp only [divisionStep, if_neg h]
    ring

theorem divisionStep_candidate_lt (m : ℕ) (s : DivisionState) (bit : Bool)
    (hr : s.remainder < m) : 2 * s.remainder + bit.toNat < 2 * m := by
  have hb : bit.toNat ≤ 1 := by cases bit <;> decide
  omega

theorem divisionStep_remainder_lt (m : ℕ) (s : DivisionState) (bit : Bool)
    (hr : s.remainder < m) : (divisionStep m s bit).remainder < m := by
  have hc := divisionStep_candidate_lt m s bit hr
  by_cases h : m ≤ 2 * s.remainder + bit.toNat <;>
    simp [divisionStep, h] <;> omega

/-- The quotient equation and bounded remainder hold after every input prefixValue. -/
theorem divisionLoop_correct (m : ℕ) (bits : List Bool) :
    ∀ (s : DivisionState) (prefixValue : ℕ),
      prefixValue = s.quotient * m + s.remainder → s.remainder < m →
      binaryValueLoop prefixValue bits =
          (divisionLoop m s bits).quotient * m + (divisionLoop m s bits).remainder ∧
        (divisionLoop m s bits).remainder < m := by
  induction bits with
  | nil => intro s prefixValue he hr; exact ⟨he, hr⟩
  | cons bit rest ih =>
    intro s prefixValue he hr
    apply ih (divisionStep m s bit) (2 * prefixValue + bit.toNat)
    · rw [he, divisionStep_decomposition]
    · exact divisionStep_remainder_lt m s bit hr

theorem restoringDivision_decomposition (m : ℕ) (hm : 0 < m) (bits : List Bool) :
    binaryValueMSB bits = (restoringDivision m bits).quotient * m +
        (restoringDivision m bits).remainder ∧
      (restoringDivision m bits).remainder < m :=
  divisionLoop_correct m bits ⟨0, 0⟩ 0 (by simp) hm

theorem restoringDivision_remainder (m : ℕ) (hm : 0 < m) (bits : List Bool) :
    (restoringDivision m bits).remainder = binaryValueMSB bits % m := by
  have h := restoringDivision_decomposition m hm bits
  rw [h.1]
  simp [Nat.add_mod, Nat.mod_eq_of_lt h.2]

theorem restoringDivision_quotient (m : ℕ) (hm : 0 < m) (bits : List Bool) :
    (restoringDivision m bits).quotient = binaryValueMSB bits / m := by
  have h := restoringDivision_decomposition m hm bits
  rw [h.1, Nat.mul_comm (restoringDivision m bits).quotient m,
    Nat.mul_add_div hm, Nat.div_eq_of_lt h.2, add_zero]

end CatalyticTreeEval.BinaryArithmetic
end

/- Proof source: Solutions.CatalyticTreeEvaluation.RestoringRound -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.BinaryArithmetic

open CatalyticTreeEval.Contracts

theorem restoredBits_value (a b : ℕ → Bool) (width : ℕ) :
    RippleAdder.bankValue (restoredBits a b width) width =
      if RippleAdder.bankValue b width ≤ RippleAdder.bankValue a width
      then RippleAdder.bankValue a width - RippleAdder.bankValue b width
      else RippleAdder.bankValue a width := by
  have hs := RippleSubtractor.bankValue_subtract a b width
  have hcmp := RippleSubtractor.carryAt_subtract_iff a b width
  change RippleSubtractor.carryAt a b true width = true ↔
    RippleAdder.bankValue b width ≤ RippleAdder.bankValue a width at hcmp
  by_cases hc : RippleSubtractor.carryAt a b true width = true
  · simp only [restoredBits, hc, ↓reduceIte, if_pos (hcmp.1 hc)]
    rw [hc] at hs
    simp only [Bool.toNat_true, mul_one] at hs
    change RippleAdder.bankValue (RippleSubtractor.sumAt a b true) width +
      2 ^ width + RippleAdder.bankValue b width = RippleAdder.bankValue a width + 2 ^ width at hs
    omega
  · have hfalse : RippleSubtractor.carryAt a b true width = false := by
      cases h : RippleSubtractor.carryAt a b true width <;> simp_all
    have hncmp : ¬RippleAdder.bankValue b width ≤ RippleAdder.bankValue a width :=
      fun h => hc (hcmp.2 h)
    simp only [restoredBits, hfalse, Bool.false_eq_true, ↓reduceIte, if_neg hncmp]
    rw [hfalse] at hs
    simp only [Bool.toNat_false, mul_zero, add_zero] at hs
    have ha := RippleAdder.bankValue_add (RippleSubtractor.sumAt a b true) b false width
    have hout := RippleSubtractor.bankValue_lt
      (RippleAdder.sumAt (RippleSubtractor.sumAt a b true) b false) width
    change RippleAdder.bankValue (RippleSubtractor.sumAt a b true) width +
      RippleAdder.bankValue b width = RippleAdder.bankValue a width + 2 ^ width at hs
    change RippleAdder.bankValue
      (RippleAdder.sumAt (RippleSubtractor.sumAt a b true) b false) width < 2 ^ width at hout
    cases hcarry : RippleAdder.carryAt (RippleSubtractor.sumAt a b true) b false width <;>
      rw [hcarry] at ha <;> simp only [Bool.toNat_true, Bool.toNat_false, mul_one,
        mul_zero, add_zero] at ha <;> omega

theorem shift_carry_false (a b : ℕ → Bool) (incoming : Bool) (width : ℕ)
    (hfit : 2 * RippleAdder.bankValue a width + incoming.toNat < 2 ^ width) :
    ShiftAppend.carryAt a b incoming width = false := by
  have h := ShiftAppend.bankValue_append a b incoming width
  change RippleAdder.bankValue (ShiftAppend.sumAt a b incoming) width +
    2 ^ width * (ShiftAppend.carryAt a b incoming width).toNat =
    2 * RippleAdder.bankValue a width + incoming.toNat at h
  cases hc : ShiftAppend.carryAt a b incoming width with
  | false => rfl
  | true => rw [hc] at h; simp only [Bool.toNat_true, mul_one] at h; omega

theorem shift_value (a b : ℕ → Bool) (incoming : Bool) (width : ℕ)
    (hfit : 2 * RippleAdder.bankValue a width + incoming.toNat < 2 ^ width) :
    RippleAdder.bankValue (ShiftAppend.sumAt a b incoming) width =
      2 * RippleAdder.bankValue a width + incoming.toNat := by
  have h := ShiftAppend.bankValue_append a b incoming width
  change RippleAdder.bankValue (ShiftAppend.sumAt a b incoming) width +
    2 ^ width * (ShiftAppend.carryAt a b incoming width).toNat =
    2 * RippleAdder.bankValue a width + incoming.toNat at h
  rw [shift_carry_false a b incoming width hfit] at h
  simpa only [Bool.toNat_false, mul_zero, add_zero] using h

/-- The actual shift/trial-subtract/conditional-restore arithmetic is exactly
one bounded restoring-division step. -/
theorem nextRemainderBits_correct (a b : ℕ → Bool) (incoming : Bool) (width : ℕ)
    (hr : RippleAdder.bankValue a width < RippleAdder.bankValue b width)
    (hcap : 2 * RippleAdder.bankValue b width ≤ 2 ^ width) :
    RippleAdder.bankValue (nextRemainderBits a b incoming width) width =
      (divisionStep (RippleAdder.bankValue b width)
        ⟨0, RippleAdder.bankValue a width⟩ incoming).remainder := by
  have hc := divisionStep_candidate_lt (RippleAdder.bankValue b width)
    ⟨0, RippleAdder.bankValue a width⟩ incoming hr
  have hf : 2 * RippleAdder.bankValue a width + incoming.toNat < 2 ^ width :=
    hc.trans_le hcap
  rw [nextRemainderBits, restoredBits_value, shift_value a b incoming width hf]
  by_cases h : RippleAdder.bankValue b width ≤
      2 * RippleAdder.bankValue a width + incoming.toNat <;> simp [divisionStep, h]

end CatalyticTreeEval.BinaryArithmetic
end

/- Proof source: Solutions.CatalyticTreeEvaluation.RestoringRoundMachine -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.RestoringRound

open CatalyticMatching.General NativeRoundSupport

def SameIO {A B : Main.Machine} (c : Config A) (d : Config B) : Prop :=
  d.inputHead = c.inputHead ∧ d.catalystHead = c.catalystHead ∧
    d.catalyst = c.catalyst ∧ d.output = c.output

theorem clear_exec {N : Main.Machine} (input : List Bool) (c : Config N)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    ∃ d : Config clearCarry,
      FirstExit (clearCarry.step input) (fun _ _ => True) {d | d.state = none}
        (startOn clearCarry c) d 1 ∧
      d.workHead = c.workHead ∧ d.work = Function.update c.work c.workHead false ∧ SameIO c d := by
  let cc := startOn clearCarry c
  let d := NativeLiteral.finished .stay 0 (some false) cc
  have H := forget (NativeLiteral.firstExit .stay 0 (some false) input cc hi hc)
  refine ⟨d, ?_, rfl, rfl, ?_⟩
  · simpa [d, cc, clearCarry, NativeLiteral.live, NativeLiteral.position, startOn,
      NativeLiteral.machine] using H
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The actual native underflow path: rewind, restore by addition, and clear
the carry delimiter. All data stay on the same physical tapes. -/
theorem restore_exec {N : Main.Machine} (input : List Bool) (c : Config N)
    (base width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base + 6 + 3 * width)
    (hmarker : c.work (base + 3) = false)
    (hbank : RippleAdder.bankContents c.work (base + 6) width a b) :
    ∃ d : Config restore,
      FirstExit (restore.step input) (fun _ _ => True) {d | d.state = none}
        (startOn restore c) d (8 * width + 8) ∧
      d.workHead = base + 6 + 3 * width ∧
      d.work = Function.update
        (RippleAdder.prefixWork c.work (base + 6) a b false width)
        (base + 6 + 3 * width) false ∧ SameIO c d := by
  let cr := startOn (TaggedRewind.machine true) c
  let dr := TaggedRewind.cursor cr (base + 6) none
  have HR := forget (TaggedRewind.firstExit input cr base width hi hc hmarker
    (fun i hi => (hbank.2 i hi).1))
  have HR' : FirstExit ((TaggedRewind.machine true).step input) (fun _ _ => True)
      {d | d.state = none} cr dr (3 * width + 6) := by
    simpa [dr, TaggedRewind.leftCursor, TaggedRewind.cursor, cr, hhead, startOn,
      TaggedRewind.machine] using HR
  let ca := startOn RippleAdder.machine dr
  let da := RippleAdder.finished ca (base + 6) width a b false
  have HA := forget (RippleAdder.bank_firstExit input ca (base + 6) width a b false hi hc hbank)
  have HA' : FirstExit (RippleAdder.machine.step input) (fun _ _ => True) {d | d.state = none}
      (startOn RippleAdder.machine dr) da (5 * width + 1) := by
    simpa [da, ca, dr, cr, TaggedRewind.cursor, RippleAdder.cursor, startOn,
      RippleAdder.machine] using HA
  obtain ⟨dc, HC, hch, hcw, hcIO⟩ := clear_exec input da hi hc
  have HAC := seq RippleAdder.machine clearCarry input dr da dc (5 * width + 1) 1 HA' HC
  have H := seq (TaggedRewind.machine true) (Sequential.machine RippleAdder.machine clearCarry)
    input c dr (Sequential.rightConfig RippleAdder.machine clearCarry dc)
    (3 * width + 6) (5 * width + 1 + 1) HR' HAC
  let d := Sequential.rightConfig (TaggedRewind.machine true)
    (Sequential.machine RippleAdder.machine clearCarry)
    (Sequential.rightConfig RippleAdder.machine clearCarry dc)
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · simpa only [restore, show 3 * width + 6 + (5 * width + 1 + 1) = 8 * width + 8 by omega]
      using H
  · change dc.workHead = _
    exact hch
  · change dc.work = _
    rw [hcw]
    simp only [da, ca, dr, cr, RippleAdder.finished, TaggedRewind.cursor, startOn,
      Function.update_idem]
  · exact hcIO

theorem acceptOrRestore_exec {N : Main.Machine} (input : List Bool) (c : Config N)
    (base width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base + 6 + 3 * width)
    (hmarker : c.work (base + 3) = false)
    (hslots : ∀ i < width, c.work (base + 6 + 3 * i) = true ∧
      c.work (base + 6 + 3 * i + 1) = a i ∧
      c.work (base + 6 + 3 * i + 2) = b i) :
    ∃ d : Config acceptOrRestore,
      FirstExit (acceptOrRestore.step input) (fun _ _ => True) {d | d.state = none}
        (startOn acceptOrRestore c) d
        (if c.work (base + 6 + 3 * width) then 2 else 8 * width + 9) ∧
      d.workHead = base + 6 + 3 * width ∧
      d.work = (if c.work (base + 6 + 3 * width)
        then Function.update c.work (base + 6 + 3 * width) false
        else Function.update (RippleAdder.prefixWork c.work (base + 6) a b false width)
          (base + 6 + 3 * width) false) ∧ SameIO c d := by
  cases hflag : c.work (base + 6 + 3 * width) with
  | true =>
    obtain ⟨dc, HC, hch, hcw, hIO⟩ := clear_exec input c hi hc
    have H := branch_true clearCarry restore input c dc 1
      (by rw [hhead, hflag]) hi hc HC
    refine ⟨Branch.leftConfig clearCarry restore dc, ?_, hch.trans hhead, ?_, hIO⟩
    · simpa only [acceptOrRestore, hflag, Bool.true_eq, ↓reduceIte] using H
    · change dc.work = _
      simpa only [hflag, Bool.true_eq, ↓reduceIte, hhead] using hcw
  | false =>
    obtain ⟨dr, HR, hrh, hrw, hIO⟩ := restore_exec input c base width a b hi hc
      hhead hmarker ⟨hflag, hslots⟩
    have H := branch_false clearCarry restore input c dr (8 * width + 8)
      (by rw [hhead, hflag]) hi hc HR
    refine ⟨Branch.rightConfig clearCarry restore dr, ?_, hrh, ?_, hIO⟩
    · simpa only [acceptOrRestore, hflag, Bool.false_eq_true, ↓reduceIte,
        show 1 + (8 * width + 8) = 8 * width + 9 by omega] using H
    · change dr.work = _
      simpa only [hflag, Bool.false_eq_true, ↓reduceIte] using hrw

end CatalyticTreeEval.Contracts.RestoringRound
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeLaneFlagCopy -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeLaneFlagCopy

open CatalyticMatching.General NativeRoundSupport
open RestoringRound (SameIO)

theorem forward_position {lanes : ℕ} (source target : Fin lanes) (base : ℕ) :
    NativeLiteral.position (forward source target) (base + source.val) (distance source target) =
      base + target.val := by
  by_cases h : source.val ≤ target.val
  · simp only [forward, distance, if_pos h, NativeLiteral.position_right]
    omega
  · simp only [forward, distance, if_neg h, NativeLiteral.position_left]
    omega

theorem backward_position {lanes : ℕ} (source target : Fin lanes) (base : ℕ) :
    NativeLiteral.position (backward source target) (base + target.val) (distance source target) =
      base + source.val := by
  by_cases h : source.val ≤ target.val
  · simp only [backward, distance, if_pos h, NativeLiteral.position_left]
    omega
  · simp only [backward, distance, if_neg h, NativeLiteral.position_right]
    omega

theorem literal_position_bound (direction : Move) (head moves bound : ℕ)
    (hstart : head < bound) (hfinish : NativeLiteral.position direction head moves < bound) :
    ∀ u ≤ moves, NativeLiteral.position direction head u < bound := by
  intro u hu
  cases direction with
  | left => rw [NativeLiteral.position_left] at *; omega
  | right => rw [NativeLiteral.position_right] at *; omega
  | stay =>
    have hs : ∀ n, NativeLiteral.position .stay head n = head := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simpa only [NativeLiteral.position, Move.apply] using ih
    rw [hs]
    exact hstart

theorem literal_visits {N : Main.Machine} (direction : Move) (moves : ℕ) (literal : Option Bool)
    (input : List Bool) (c : Config N) (bound : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hstart : c.workHead < bound)
    (hfinish : NativeLiteral.position direction c.workHead moves < bound) :
    Visits input (startOn (NativeLiteral.machine direction moves literal) c) (moves + 1) bound := by
  let cc := startOn (NativeLiteral.machine direction moves literal) c
  have he : startOn (NativeLiteral.machine direction moves literal) c =
      NativeLiteral.live direction moves literal cc 0 (by omega) := by
    simp [cc, startOn, NativeLiteral.live, NativeLiteral.machine, NativeLiteral.position]
  rw [he]
  intro u hu d hd
  by_cases hm : u ≤ moves
  · rw [NativeLiteral.run_live direction moves literal input cc hi hc u hm] at hd
    cases Option.some.inj hd
    exact literal_position_bound direction c.workHead moves bound hstart hfinish u hm
  · have heq : u = moves + 1 := by omega
    subst u
    rw [runFrom_succ, NativeLiteral.run_live direction moves literal input cc hi hc moves le_rfl,
      Option.bind_some, NativeLiteral.step_finish direction moves literal input cc hi hc] at hd
    cases Option.some.inj hd
    exact hfinish

theorem literal_none_frames {N : Main.Machine} (direction : Move) (moves : ℕ)
    (input : List Bool) (c : Config N)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    Frames input c (startOn (NativeLiteral.machine direction moves none) c) (moves + 1) ⟨∅,∅⟩ := by
  let cc := startOn (NativeLiteral.machine direction moves none) c
  have he : startOn (NativeLiteral.machine direction moves none) c =
      NativeLiteral.live direction moves none cc 0 (by omega) := by
    simp [cc, startOn, NativeLiteral.live, NativeLiteral.machine, NativeLiteral.position]
  rw [he]
  intro u hu d hd
  by_cases hm : u ≤ moves
  · rw [NativeLiteral.run_live direction moves none input cc hi hc u hm] at hd
    cases Option.some.inj hd
    exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  · have heq : u = moves + 1 := by omega
    subst u
    rw [runFrom_succ, NativeLiteral.run_live direction moves none input cc hi hc moves le_rfl,
      Option.bind_some, NativeLiteral.step_finish direction moves none input cc hi hc] at hd
    cases Option.some.inj hd
    refine ⟨?_, rfl, fun _ _ => rfl⟩
    intro p hp
    simp [NativeLiteral.finished, cc, startOn, Function.update_eq_self]

theorem arm_exec {N : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (input : List Bool) (c : Config N) (base : ℕ) (bit : Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base + source.val) :
    ∃ d : Config (arm source target bit),
      FirstExit ((arm source target bit).step input) (fun _ _ => True) {d | d.state = none}
        (startOn (arm source target bit) c) d (2 * distance source target + 2) ∧
      Visits input (startOn (arm source target bit) c) (2 * distance source target + 2) (base + lanes) ∧
      Frames input c (startOn (arm source target bit) c) (2 * distance source target + 2)
        ⟨{base + target.val},∅⟩ ∧
      d.workHead = base + source.val ∧ d.work = Function.update c.work (base + target.val) bit ∧ SameIO c d := by
  let F := NativeLiteral.machine (forward source target) (distance source target) (some bit)
  let B := NativeLiteral.machine (backward source target) (distance source target) none
  let cf := startOn F c
  let df := NativeLiteral.finished (forward source target) (distance source target) (some bit) cf
  have HF0 := NativeLiteral.firstExit (forward source target) (distance source target) (some bit) input cf hi hc
  have HF : FirstExit (F.step input) (fun _ _ => True) {d | d.state = none} cf df (distance source target + 1) := by
    simpa [F, cf, df, NativeLiteral.live, startOn, NativeLiteral.machine, NativeLiteral.position] using forget HF0
  have VF := literal_visits (forward source target) (distance source target) (some bit)
    input c (base + lanes) hi hc (by omega) (by rw [hhead, forward_position]; omega)
  have FF : Frames input c cf (distance source target + 1) ⟨{base + target.val},∅⟩ := by
    have H := frames_of_contract HF0
    simpa [Frames, Frame, cf, F, NativeLiteral.live, startOn, NativeLiteral.machine,
      NativeLiteral.position, hhead, forward_position] using H
  have hfh : df.workHead = base + target.val := by
    simp [df, cf, NativeLiteral.finished, startOn, hhead, forward_position]
  let cb := startOn B df
  let db := NativeLiteral.finished (backward source target) (distance source target) none cb
  have HB0 := NativeLiteral.firstExit (backward source target) (distance source target) none input cb hi hc
  have HB : FirstExit (B.step input) (fun _ _ => True) {d | d.state = none} cb db (distance source target + 1) := by
    simpa [B, cb, db, NativeLiteral.live, startOn, NativeLiteral.machine, NativeLiteral.position] using forget HB0
  have VB := literal_visits (backward source target) (distance source target) none input df (base + lanes)
    hi hc (by omega) (by rw [hfh, backward_position]; omega)
  have FB := (literal_none_frames (backward source target) (distance source target) input df hi hc).mono
    (G := ⟨{base + target.val},∅⟩) (by simp) (Set.Subset.refl _)
  have H := seq F B input c df db (distance source target + 1) (distance source target + 1) HF HB
  have V := visits_seq F B input c df db (distance source target + 1) (distance source target + 1)
    (base + lanes) HF HB VF VB
  have Fr := frames_seq F B input c df db (distance source target + 1) (distance source target + 1)
    ⟨{base + target.val},∅⟩ HF HB FF FB
  refine ⟨Sequential.rightConfig F B db, ?_, ?_, ?_, ?_, ?_, ⟨rfl,rfl,rfl,rfl⟩⟩
  · simpa only [arm, F, B, show distance source target + 1 + (distance source target + 1) =
      2 * distance source target + 2 by omega] using H
  · simpa only [arm, F, B, show distance source target + 1 + (distance source target + 1) =
      2 * distance source target + 2 by omega] using V
  · simpa only [arm, F, B, show distance source target + 1 + (distance source target + 1) =
      2 * distance source target + 2 by omega] using Fr
  · change db.workHead = _
    simp [db, cb, NativeLiteral.finished, startOn, hfh, backward_position]
  · change db.work = _
    simp [db, cb, df, cf, NativeLiteral.finished, startOn, Function.update_eq_self,
      hhead, forward_position]

/-- Fixed-lane flag copy, with its complete first halt, exact dispatch/move
time, singleton writable frame, tight row-zero work bound, and caller return. -/
theorem machine_exec {N : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (input : List Bool) (c : Config N) (base : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base + source.val) :
    ∃ d : Config (machine source target),
      FirstExit ((machine source target).step input)
        (fun _ e => e.workHead < base + lanes ∧ Frame ⟨{base + target.val},∅⟩ c e)
        {d | d.state = none} (startOn (machine source target) c) d (2 * distance source target + 3) ∧
      d.workHead = base + source.val ∧
      d.work = Function.update c.work (base + target.val) (c.work (base + source.val)) ∧ SameIO c d := by
  cases hb : c.work (base + source.val) with
  | true =>
    obtain ⟨da, HA, VA, FA, hah, haw, haIO⟩ := arm_exec source target input c base true hi hc hhead
    have HE := branch_true (arm source target true) (arm source target false) input c da
      (2 * distance source target + 2) (by rw [hhead, hb]) hi hc HA
    have VE := visits_branch_true (arm source target true) (arm source target false) input c da
      (2 * distance source target + 2) (base + lanes) (by rw [hhead, hb]) hi hc HA (by omega) VA
    have FE := frames_branch_true (arm source target true) (arm source target false) input c da
      (2 * distance source target + 2) ⟨{base + target.val},∅⟩ (by rw [hhead, hb]) hi hc HA FA
    let d := Branch.leftConfig (arm source target true) (arm source target false) da
    have H : FirstExit ((machine source target).step input)
        (fun _ e => e.workHead < base + lanes ∧ Frame ⟨{base + target.val},∅⟩ c e)
        {d | d.state = none} (startOn (machine source target) c) d (1 + (2 * distance source target + 2)) :=
      { result := HE.result
        during := fun u hu e he => ⟨VE u hu e he, FE u hu e he⟩
        exit_mem := HE.exit_mem
        cut := HE.cut }
    refine ⟨d, ?_, hah, ?_, haIO⟩
    · simpa only [show 1 + (2 * distance source target + 2) = 2 * distance source target + 3 by omega] using H
    · change da.work = _
      simpa only [hb] using haw
  | false =>
    obtain ⟨da, HA, VA, FA, hah, haw, haIO⟩ := arm_exec source target input c base false hi hc hhead
    have HE := branch_false (arm source target true) (arm source target false) input c da
      (2 * distance source target + 2) (by rw [hhead, hb]) hi hc HA
    have VE := visits_branch_false (arm source target true) (arm source target false) input c da
      (2 * distance source target + 2) (base + lanes) (by rw [hhead, hb]) hi hc HA (by omega) VA
    have FE := frames_branch_false (arm source target true) (arm source target false) input c da
      (2 * distance source target + 2) ⟨{base + target.val},∅⟩ (by rw [hhead, hb]) hi hc HA FA
    let d := Branch.rightConfig (arm source target true) (arm source target false) da
    have H : FirstExit ((machine source target).step input)
        (fun _ e => e.workHead < base + lanes ∧ Frame ⟨{base + target.val},∅⟩ c e)
        {d | d.state = none} (startOn (machine source target) c) d (1 + (2 * distance source target + 2)) :=
      { result := HE.result
        during := fun u hu e he => ⟨VE u hu e he, FE u hu e he⟩
        exit_mem := HE.exit_mem
        cut := HE.cut }
    refine ⟨d, ?_, hah, ?_, haIO⟩
    · simpa only [show 1 + (2 * distance source target + 2) = 2 * distance source target + 3 by omega] using H
    · change da.work = _
      simpa only [hb] using haw

end CatalyticTreeEval.Contracts.NativeLaneFlagCopy
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeMarkerSeek -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeMarkerSeek

open CatalyticMatching.General

theorem step_move (direction : Move) (padding : ℕ) (input : List Bool)
    (c : Config (machine direction padding)) (u : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (scan : u % (padding + 1) = 0 →
      c.work (NativeLiteral.position direction c.workHead u) = false) :
    (machine direction padding).step input (cursor direction padding c u) =
      some (cursor direction padding c (u + 1)) := by
  have gate : ¬ (u % (padding + 1) = 0 ∧
      c.work (NativeLiteral.position direction c.workHead u) = true) := by
    rintro ⟨phase, bit⟩
    rw [scan phase] at bit
    contradiction
  have next : (u % (padding + 1) + 1) % (padding + 1) = (u + 1) % (padding + 1) := by
    simp only [Nat.add_mod, Nat.mod_mod]
  simp [Machine.step, machine, cursor, gate, next, NativeLiteral.position,
    Move.apply, hi, hc, Function.update_eq_self]

theorem run_live (direction : Move) (padding : ℕ) (input : List Bool)
    (c : Config (machine direction padding)) (rows : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (markers : ∀ i < rows,
      c.work (NativeLiteral.position direction c.workHead (i * (padding + 1))) = false) :
    ∀ u ≤ rows * (padding + 1),
      runFrom ((machine direction padding).step input) (cursor direction padding c 0) u =
        some (cursor direction padding c u) := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
      intro hu
      rw [runFrom_succ, ih (by omega), Option.bind_some]
      apply step_move direction padding input c u hi hc
      intro phase
      have rowBound : u / (padding + 1) < rows :=
        Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using (show u < rows * (padding + 1) by omega))
      have equal : u / (padding + 1) * (padding + 1) = u := by
        have h := Nat.div_add_mod' u (padding + 1)
        omega
      simpa only [equal] using markers (u / (padding + 1)) rowBound

theorem step_finish (direction : Move) (padding : ℕ) (input : List Bool)
    (c : Config (machine direction padding)) (rows : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (marker : c.work (NativeLiteral.position direction c.workHead (rows * (padding + 1))) = true) :
    (machine direction padding).step input (cursor direction padding c (rows * (padding + 1))) =
      some (finished direction padding c rows) := by
  simp [Machine.step, machine, cursor, finished, marker, Move.apply, hi, hc,
    Function.update_eq_self]

/-- Searching an actual marker track preserves all data and charges every
physical movement. Width/row count occur only in the contract, never the code. -/
theorem firstExit (direction : Move) (padding : ℕ) (input : List Bool)
    (c : Config (machine direction padding)) (rows : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (markers : ∀ i < rows,
      c.work (NativeLiteral.position direction c.workHead (i * (padding + 1))) = false)
    (marker : c.work (NativeLiteral.position direction c.workHead (rows * (padding + 1))) = true) :
    FirstExit ((machine direction padding).step input)
      (fun _ d => (Envelope.mk 0
        (max c.workHead (NativeLiteral.position direction c.workHead (rows * (padding + 1))) + 1)
        c.catalystHead (c.catalystHead + 1)).Contains d ∧ SameOutside ⟨∅, ∅⟩ c d)
      {d | d.state = none} (cursor direction padding c 0)
      (finished direction padding c rows) (rows * (padding + 1) + 1) where
  result := by
    rw [runFrom_succ, run_live direction padding input c rows hi hc markers _ le_rfl,
      Option.bind_some]
    exact step_finish direction padding input c rows hi hc marker
  during u hu d hd := by
    by_cases h : u ≤ rows * (padding + 1)
    · rw [run_live direction padding input c rows hi hc markers u h] at hd
      cases Option.some.inj hd
      constructor
      · have bound := NativeLaneFlagCopy.literal_position_bound direction c.workHead
          (rows * (padding + 1))
          (max c.workHead (NativeLiteral.position direction c.workHead (rows * (padding + 1))) + 1)
          (by omega) (by omega) u h
        exact ⟨Nat.zero_le _, bound, le_rfl, Nat.lt_succ_self _⟩
      · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩
    · have last : u = rows * (padding + 1) + 1 := by omega
      subst u
      rw [runFrom_succ, run_live direction padding input c rows hi hc markers _ le_rfl,
        Option.bind_some, step_finish direction padding input c rows hi hc marker] at hd
      cases Option.some.inj hd
      constructor
      · exact ⟨Nat.zero_le _, by dsimp [finished]; omega, le_rfl, Nat.lt_succ_self _⟩
      · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl⟩
  exit_mem := rfl
  cut u hu d hd := by
    rw [run_live direction padding input c rows hi hc markers u (by omega)] at hd
    cases Option.some.inj hd
    exact Option.some_ne_none _

end CatalyticTreeEval.Contracts.NativeMarkerSeek
end

/- Proof source: Solutions.CatalyticTreeEvaluation.WorkLanes -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

theorem distance_pos {lanes : ℕ} (lane : Fin lanes) : 0 < distance lane := by
  dsimp [distance]
  omega

theorem address_injective {lanes : ℕ} (lane : Fin lanes) (base : ℕ) :
    Function.Injective (address lane base) := by
  intro p q h
  dsimp [address] at h
  nlinarith

theorem address_ne_marker {lanes : ℕ} (lane : Fin lanes) (base p q : ℕ) :
    address lane base p ≠ markerAddress lanes base q := by
  intro equal
  have offset : (lanes + 1) * p + lane.val = (lanes + 1) * q + lanes := by
    dsimp [address, markerAddress] at equal
    omega
  have h := congrArg (fun n => n % (lanes + 1)) offset
  have hl : lane.val < lanes + 1 := by omega
  simp [Nat.add_mod,
    Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (Nat.lt_succ_self lanes)] at h
  omega

theorem marker_ne_address {lanes : ℕ} (lane : Fin lanes) (base p q : ℕ) :
    markerAddress lanes base p ≠ address lane base q :=
  (address_ne_marker lane base q p).symm

theorem update_matches {lanes : ℕ} (lane : Fin lanes) (base : ℕ)
    (source physical : ℕ → Bool) (h : Matches lane base source physical) (p : ℕ) (b : Bool) :
    Matches lane base (Function.update source p b)
      (Function.update physical (address lane base p) b) := by
  intro q
  by_cases hp : q = p
  · subst q; simp
  · have haddr : address lane base q ≠ address lane base p :=
      fun he => hp (address_injective lane base he)
    simp [Function.update_of_ne hp, Function.update_of_ne haddr, h q]

theorem update_origin {lanes : ℕ} (lane : Fin lanes) (base : ℕ)
    (physical : ℕ → Bool) (h : OriginTrack lanes base physical) (p : ℕ) (b : Bool) :
    OriginTrack lanes base (Function.update physical (address lane base p) b) := by
  intro q
  rw [Function.update_of_ne (marker_ne_address lane base q p)]
  exact h q

theorem address_lanes_injective {lanes : ℕ} (left right : Fin lanes) (base p q : ℕ)
    (equal : address left base p = address right base q) : left = right ∧ p = q := by
  have offset : (lanes + 1) * p + left.val = (lanes + 1) * q + right.val := by
    dsimp [address] at equal
    omega
  have h := congrArg (fun n => n % (lanes + 1)) offset
  have hl : left.val < lanes + 1 := by omega
  have hr : right.val < lanes + 1 := by omega
  simp [Nat.add_mod, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] at h
  have lanesEqual : left = right := Fin.ext h
  subst right
  exact ⟨rfl, address_injective left base equal⟩

theorem update_other_lane {lanes : ℕ} (lane other : Fin lanes) (base : ℕ)
    (physical : ℕ → Bool) (different : other ≠ lane) (p q : ℕ) (b : Bool) :
    (Function.update physical (address lane base p) b) (address other base q) =
      physical (address other base q) := by
  apply Function.update_of_ne
  intro equal
  exact different (address_lanes_injective other lane base q p equal).1

theorem step_outward (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (r : Fin (lanes + 1)) (head : ℕ)
    (positive : 0 < r.val)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length) :
    (machine A lanes lane).step input
      (snapshot A lanes lane source physical (some (outward A lanes q r)) head) =
      some (snapshot A lanes lane source physical
        (some (outward A lanes q (predecessor r))) (head + 1)) := by
  simp [Machine.step, snapshot, machine, instruction, outward, quietInstruction,
    positive.ne', Move.apply, hi, hc, Function.update_eq_self]

theorem step_marker (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (head : ℕ)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length) :
    (machine A lanes lane).step input
      (snapshot A lanes lane source physical (some (outward A lanes q ⟨0, by omega⟩)) head) =
      some (snapshot A lanes lane source physical
        (some (inward A lanes q (physical head) (predecessor (counter lane)))) (head - 1)) := by
  simp [Machine.step, snapshot, machine, instruction, outward, quietInstruction,
    Move.apply, hi, hc, Function.update_eq_self]

theorem step_inward (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (origin : Bool) (r : Fin (lanes + 1)) (head : ℕ)
    (positive : 0 < r.val)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length) :
    (machine A lanes lane).step input
      (snapshot A lanes lane source physical (some (inward A lanes q origin r)) head) =
      some (snapshot A lanes lane source physical
        (some (inward A lanes q origin (predecessor r))) (head - 1)) := by
  simp [Machine.step, snapshot, machine, instruction, inward, quietInstruction,
    positive.ne', Move.apply, hi, hc, Function.update_eq_self]

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof source: Solutions.CatalyticTreeEvaluation.WorkLaneGeometry -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

theorem decodeMove_moveCode (move : Move) : decodeMove (moveCode move) = move := by
  cases move <;> rfl

theorem address_add_distance {lanes : ℕ} (lane : Fin lanes) (base p : ℕ) :
    address lane base p + distance lane = markerAddress lanes base p := by
  dsimp [address, distance, markerAddress]
  omega

theorem address_add_stride {lanes : ℕ} (lane : Fin lanes) (base p : ℕ) :
    address lane base (p + 1) = address lane base p + (lanes + 1) := by
  simp [address, Nat.mul_add]
  omega

theorem padded_work_move {lanes : ℕ} (lane : Fin lanes) (base p : ℕ) (move : Move) :
    drift (moveCode (clippedMove (decide (p = 0)) move))
      ((clippedMove (decide (p = 0)) move).apply (address lane base p)) lanes =
        address lane base (move.apply p) := by
  cases move with
  | left =>
    cases p with
    | zero => simp [clippedMove, moveCode, drift, Move.apply]
    | succ p =>
      simp only [Nat.succ_ne_zero, decide_false, clippedMove, Bool.false_eq_true,
        ↓reduceIte, moveCode, Move.apply, drift, Nat.add_sub_cancel]
      simp only [address, Nat.mul_add, Nat.mul_one]
      omega
  | stay => simp [clippedMove, moveCode, drift, Move.apply]
  | right =>
    simp [clippedMove, moveCode, drift, Move.apply, address, Nat.mul_add]
    omega

theorem address_lt_prefix {lanes : ℕ} (lane : Fin lanes) (base p bound : ℕ)
    (hp : p < bound) : address lane base p < base + (lanes + 1) * bound := by
  have H := Nat.mul_le_mul_left (lanes + 1) (show p + 1 ≤ bound by omega)
  simp only [Nat.mul_add, Nat.mul_one] at H
  dsimp [address]
  omega

theorem marker_lt_prefix (lanes base p bound : ℕ) (hp : p < bound) :
    markerAddress lanes base p < base + (lanes + 1) * bound := by
  have H := Nat.mul_le_mul_left (lanes + 1) (show p + 1 ≤ bound by omega)
  simp only [Nat.mul_add, Nat.mul_one] at H
  dsimp [markerAddress]
  omega

theorem address_le_marker {lanes : ℕ} (lane : Fin lanes) (base p : ℕ) :
    address lane base p ≤ markerAddress lanes base p := by
  dsimp [address, markerAddress]
  omega

theorem address_le_shuttle {lanes : ℕ} (lane : Fin lanes) (base p t : ℕ) :
    address lane base p ≤ address lane base p + t := by omega

theorem shuttle_le_marker {lanes : ℕ} (lane : Fin lanes) (base p t : ℕ)
    (ht : t ≤ distance lane) :
    address lane base p + t ≤ markerAddress lanes base p := by
  rw [← address_add_distance lane base p]
  omega

theorem drift_between (direction : Option Bool) (head steps t : ℕ) (ht : t ≤ steps) :
    min head (drift direction head steps) ≤ drift direction head t ∧
      drift direction head t ≤ max head (drift direction head steps) := by
  cases direction with
  | none => simp [drift]
  | some bit => cases bit <;> simp only [drift] <;> omega

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeLaneWordGeometry -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeLaneWordTransfer

open CatalyticMatching.General

theorem address_add_hop {lanes : ℕ} (lane : Fin lanes) (base p q : ℕ) :
    WorkLanes.address lane base (p + q) = WorkLanes.address lane base p + (lanes + 1) * q := by
  simp only [WorkLanes.address, Nat.mul_add]
  omega

theorem targetCell_offset {lanes : ℕ} (target : Fin lanes) (targetB : Bool) (base i : ℕ) :
    targetCell target targetB base i = base + (lanes + 1) * (7 + 3 * i) +
      (targetIndex target targetB).val := by
  simp only [targetCell, WorkLanes.address, targetIndex, Nat.mul_add]
  omega

theorem forward_position {lanes : ℕ} (source target : Fin lanes) (targetB : Bool) (base i : ℕ) :
    NativeLiteral.position
      (NativeLaneFlagCopy.forward (sourceIndex source) (targetIndex target targetB))
      (sourceCell source base i) (distance source target targetB) = targetCell target targetB base i := by
  rw [targetCell_offset]
  exact NativeLaneFlagCopy.forward_position (sourceIndex source) (targetIndex target targetB)
    (base + (lanes + 1) * (7 + 3 * i))

theorem backward_position {lanes : ℕ} (source target : Fin lanes) (targetB : Bool) (base i : ℕ) :
    NativeLiteral.position
      (NativeLaneFlagCopy.backward (sourceIndex source) (targetIndex target targetB))
      (targetCell target targetB base i) (distance source target targetB) = sourceCell source base i := by
  rw [targetCell_offset]
  exact NativeLaneFlagCopy.backward_position (sourceIndex source) (targetIndex target targetB)
    (base + (lanes + 1) * (7 + 3 * i))

theorem sourceCell_ne_targetCell {lanes : ℕ} (source target : Fin lanes) (targetB : Bool)
    (base i j : ℕ) (hne : source ≠ target) : sourceCell source base i ≠ targetCell target targetB base j := by
  intro he
  exact hne (WorkLanes.address_lanes_injective source target base _ _ he).1

theorem sourceCell_injective {lanes : ℕ} (source : Fin lanes) (base : ℕ) :
    Function.Injective (sourceCell source base) := by
  intro i j he
  have H := WorkLanes.address_injective source base he
  omega

theorem targetCell_injective {lanes : ℕ} (target : Fin lanes) (targetB : Bool) (base : ℕ) :
    Function.Injective (targetCell target targetB base) := by
  intro i j he
  have H := WorkLanes.address_injective target base he
  omega

theorem tag_outside {lanes : ℕ} (source target lane : Fin lanes) (targetB consume : Bool)
    (base width j : ℕ) :
    WorkLanes.address lane base (6 + 3 * j) ∉ (footprint source target targetB consume base width).work := by
  rintro (⟨i, hi, he⟩ | ⟨hc, i, hi, he⟩)
  · have H := (WorkLanes.address_lanes_injective lane target base _ _ he).2
    have hb : targetB.toNat ≤ 1 := by cases targetB <;> decide
    omega
  · have H := (WorkLanes.address_lanes_injective lane source base _ _ he).2
    omega

theorem marker_outside {lanes : ℕ} (source target lane : Fin lanes) (targetB consume : Bool)
    (base width : ℕ) :
    WorkLanes.address lane base 3 ∉ (footprint source target targetB consume base width).work := by
  rintro (⟨i, hi, he⟩ | ⟨hc, i, hi, he⟩)
  · have H := (WorkLanes.address_lanes_injective lane target base _ _ he).2
    omega
  · have H := (WorkLanes.address_lanes_injective lane source base _ _ he).2
    omega

theorem flag_outside {lanes : ℕ} (source target lane : Fin lanes) (targetB consume : Bool)
    (base width : ℕ) :
    WorkLanes.address lane base 0 ∉ (footprint source target targetB consume base width).work := by
  rintro (⟨i, hi, he⟩ | ⟨hc, i, hi, he⟩)
  · have H := (WorkLanes.address_lanes_injective lane target base _ _ he).2
    omega
  · have H := (WorkLanes.address_lanes_injective lane source base _ _ he).2
    omega

theorem sourceCell_bound {lanes : ℕ} (source : Fin lanes) (base width i : ℕ) (hi : i < width) :
    sourceCell source base i < base + (lanes + 1) * (7 + 3 * width) :=
  WorkLanes.address_lt_prefix source base _ _ (by omega)

theorem targetCell_bound {lanes : ℕ} (target : Fin lanes) (targetB : Bool)
    (base width i : ℕ) (hi : i < width) :
    targetCell target targetB base i < base + (lanes + 1) * (7 + 3 * width) := by
  have hb : targetB.toNat ≤ 1 := by cases targetB <;> decide
  exact WorkLanes.address_lt_prefix target base _ _ (by omega)

theorem tag_bound {lanes : ℕ} (source : Fin lanes) (base width i : ℕ) (hi : i ≤ width) :
    WorkLanes.address source base (6 + 3 * i) < base + (lanes + 1) * (7 + 3 * width) :=
  WorkLanes.address_lt_prefix source base _ _ (by omega)

theorem prefixWork_outside {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool)
    (base width : ℕ) (work : ℕ → Bool) :
    ∀ processed ≤ width, ∀ p, p ∉ (footprint source target targetB consume base width).work →
      prefixWork source target targetB consume base work processed p = work p := by
  intro processed
  induction processed with
  | zero => intro hn p hp; rfl
  | succ n ih =>
    intro hn p hp
    have htarget : p ≠ targetCell target targetB base n := by
      intro h; apply hp; exact Or.inl ⟨n, by omega, h⟩
    simp only [prefixWork]
    split_ifs with hc
    · have hsource : p ≠ sourceCell source base n := by
        intro h; apply hp; exact Or.inr ⟨hc, n, by omega, h⟩
      rw [Function.update_of_ne hsource, Function.update_of_ne htarget]
      exact ih (by omega) p hp
    · rw [Function.update_of_ne htarget]
      exact ih (by omega) p hp

theorem prefixWork_unprocessed_source {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool)
    (base processed i : ℕ) (work : ℕ → Bool) (hne : source ≠ target) (hi : processed ≤ i) :
    prefixWork source target targetB consume base work processed (sourceCell source base i) =
      work (sourceCell source base i) := by
  apply prefixWork_outside source target targetB consume base processed work processed le_rfl
  rintro (⟨j, hj, he⟩ | ⟨hc, j, hj, he⟩)
  · exact sourceCell_ne_targetCell source target targetB base i j hne he
  · have H := sourceCell_injective source base he
    omega

theorem prefixWork_target {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool)
    (base : ℕ) (work : ℕ → Bool) (hne : source ≠ target) :
    ∀ processed i, i < processed →
      prefixWork source target targetB consume base work processed (targetCell target targetB base i) =
        work (sourceCell source base i) := by
  intro processed
  induction processed with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    have hsource : targetCell target targetB base i ≠ sourceCell source base n :=
      (sourceCell_ne_targetCell source target targetB base n i hne).symm
    simp only [prefixWork]
    split_ifs
    · rw [Function.update_of_ne hsource]
      by_cases he : i = n
      · subst i; simp
      · rw [Function.update_of_ne (by intro h;exact he (targetCell_injective target targetB base h))]
        exact ih i (by omega)
    · by_cases he : i = n
      · subst i; simp
      · rw [Function.update_of_ne (by intro h;exact he (targetCell_injective target targetB base h))]
        exact ih i (by omega)

theorem prefixWork_source_consumed {lanes : ℕ} (source target : Fin lanes) (targetB : Bool)
    (base : ℕ) (work : ℕ → Bool) (hne : source ≠ target) :
    ∀ processed i, i < processed →
      prefixWork source target targetB true base work processed (sourceCell source base i) = false := by
  intro processed
  induction processed with
  | zero => intro i hi;omega
  | succ n ih =>
    intro i hi
    simp only [prefixWork,Bool.true_eq,↓reduceIte]
    by_cases he : i = n
    · subst i;simp
    · rw [Function.update_of_ne (by intro h;exact he (sourceCell_injective source base h)),
        Function.update_of_ne (sourceCell_ne_targetCell source target targetB base i n hne)]
      exact ih i (by omega)

theorem prefixWork_source_preserved {lanes : ℕ} (source target : Fin lanes) (targetB : Bool)
    (base : ℕ) (work : ℕ → Bool) (hne : source ≠ target) (processed i : ℕ) :
    prefixWork source target targetB false base work processed (sourceCell source base i) =
      work (sourceCell source base i) := by
  apply prefixWork_outside source target targetB false base processed work processed le_rfl
  rintro (⟨j,hj,he⟩|⟨hc,h⟩)
  · exact sourceCell_ne_targetCell source target targetB base i j hne he
  · cases hc

theorem frame_preserves_tags {A B : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (targetB consume : Bool) (base width : ℕ) (c : Config A) (d : Config B)
    (F : NativeRoundSupport.Frame (footprint source target targetB consume base width) c d) :
    ∀ (lane : Fin lanes) j, d.work (WorkLanes.address lane base (6 + 3 * j)) =
      c.work (WorkLanes.address lane base (6 + 3 * j)) := by
  intro lane j
  exact F.1 _ (tag_outside source target lane targetB consume base width j)

theorem frame_preserves_origin {A B : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (targetB consume : Bool) (base width : ℕ) (c : Config A) (d : Config B)
    (F : NativeRoundSupport.Frame (footprint source target targetB consume base width) c d)
    (origin : WorkLanes.OriginTrack lanes base c.work) : WorkLanes.OriginTrack lanes base d.work := by
  intro p
  rw [F.1 (WorkLanes.markerAddress lanes base p) (by
    rintro (⟨i,hi,he⟩|⟨hc,i,hi,he⟩)
    · exact WorkLanes.address_ne_marker target base _ p he.symm
    · exact WorkLanes.address_ne_marker source base _ p he.symm)]
  exact origin p

theorem frame_preserves_other_lane {A B : Main.Machine} {lanes : ℕ} (source target other : Fin lanes)
    (targetB consume : Bool) (base width : ℕ) (c : Config A) (d : Config B)
    (F : NativeRoundSupport.Frame (footprint source target targetB consume base width) c d)
    (hnt : other ≠ target) (hns : consume = true → other ≠ source) :
    ∀ p, d.work (WorkLanes.address other base p) = c.work (WorkLanes.address other base p) := by
  intro p
  apply F.1
  rintro (⟨i,hi,he⟩|⟨hc,i,hi,he⟩)
  · exact hnt (WorkLanes.address_lanes_injective other target base _ _ he).1
  · exact hns hc (WorkLanes.address_lanes_injective other source base _ _ he).1

end CatalyticTreeEval.Contracts.NativeLaneWordTransfer
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeLaneWordBit -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeLaneWordTransfer

open NativeRoundSupport
open RestoringRound (SameIO)

theorem sameIO_trans {A B C : Main.Machine} {a : Config A} {b : Config B} {c : Config C}
    (H : SameIO a b) (K : SameIO b c) : SameIO a c :=
  ⟨K.1.trans H.1, K.2.1.trans H.2.1, K.2.2.1.trans H.2.2.1, K.2.2.2.trans H.2.2.2⟩

theorem move_exec {N : Main.Machine} (direction : CatalyticMatching.General.Move) (moves : ℕ)
    (input : List Bool) (c : Config N) (target bound : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hposition : NativeLiteral.position direction c.workHead moves = target)
    (hstart : c.workHead < bound) (hend : target < bound) :
    ∃ d : Config (NativeLiteral.machine direction moves none),
      FirstExit ((NativeLiteral.machine direction moves none).step input)
        (fun _ e => e.workHead < bound ∧ Frame ⟨∅,∅⟩ c e) {d | d.state = none}
        (startOn (NativeLiteral.machine direction moves none) c) d (moves + 1) ∧
      d.workHead = target ∧ d.work = c.work ∧ SameIO c d := by
  let cc := startOn (NativeLiteral.machine direction moves none) c
  let d := NativeLiteral.finished direction moves none cc
  have H0 := NativeLiteral.firstExit direction moves none input cc hi hc
  have H : FirstExit ((NativeLiteral.machine direction moves none).step input) (fun _ _ => True)
      {d | d.state = none} cc d (moves + 1) := by
    simpa [cc, d, NativeLiteral.live, startOn, NativeLiteral.machine, NativeLiteral.position] using forget H0
  have V := NativeLaneFlagCopy.literal_visits direction moves none input c bound hi hc hstart (by rw [hposition]; exact hend)
  have F := NativeLaneFlagCopy.literal_none_frames direction moves input c hi hc
  have HF : FirstExit ((NativeLiteral.machine direction moves none).step input)
      (fun _ e => e.workHead < bound ∧ Frame ⟨∅,∅⟩ c e) {d | d.state = none}
      (startOn (NativeLiteral.machine direction moves none) c) d (moves + 1) :=
    { result := H.result
      during := fun u hu e he => ⟨V u hu e he,F u hu e he⟩
      exit_mem := H.exit_mem
      cut := H.cut }
  refine ⟨d,HF,?_,?_,⟨rfl,rfl,rfl,rfl⟩⟩
  · simpa [d,cc,NativeLiteral.finished,startOn] using hposition
  · simp [d,cc,NativeLiteral.finished,startOn,Function.update_eq_self]

theorem bitArm_exec {N : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (targetB consume : Bool) (input : List Bool) (c : Config N) (base width i : ℕ) (bit : Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = sourceCell source base i) (hindex : i < width) :
    ∃ d : Config (bitArm source target targetB consume bit),
      FirstExit ((bitArm source target targetB consume bit).step input) (fun _ _ => True)
        {d | d.state = none} (startOn (bitArm source target targetB consume bit) c) d
        (2 * distance source target targetB + 2) ∧
      Visits input (startOn (bitArm source target targetB consume bit) c)
        (2 * distance source target targetB + 2) (base + (lanes + 1) * (7 + 3 * width)) ∧
      Frames input c (startOn (bitArm source target targetB consume bit) c)
        (2 * distance source target targetB + 2) (footprint source target targetB consume base width) ∧
      d.workHead = sourceCell source base i ∧
      d.work = (if consume then
        Function.update (Function.update c.work (targetCell target targetB base i) bit)
          (sourceCell source base i) false
        else Function.update c.work (targetCell target targetB base i) bit) ∧ SameIO c d := by
  let F := NativeLiteral.machine
    (NativeLaneFlagCopy.forward (sourceIndex source) (targetIndex target targetB))
    (distance source target targetB) (some bit)
  let B := NativeLiteral.machine
    (NativeLaneFlagCopy.backward (sourceIndex source) (targetIndex target targetB))
    (distance source target targetB) (if consume then some false else none)
  let cf := startOn F c
  let df := NativeLiteral.finished
    (NativeLaneFlagCopy.forward (sourceIndex source) (targetIndex target targetB))
    (distance source target targetB) (some bit) cf
  have HF0 := NativeLiteral.firstExit
    (NativeLaneFlagCopy.forward (sourceIndex source) (targetIndex target targetB))
    (distance source target targetB) (some bit) input cf hi hc
  have HF : FirstExit (F.step input) (fun _ _ => True) {d | d.state = none}
      cf df (distance source target targetB + 1) := by
    simpa [F, cf, df, NativeLiteral.live, startOn, NativeLiteral.machine,
      NativeLiteral.position] using forget HF0
  have VF := NativeLaneFlagCopy.literal_visits
    (NativeLaneFlagCopy.forward (sourceIndex source) (targetIndex target targetB))
    (distance source target targetB) (some bit) input c
    (base + (lanes + 1) * (7 + 3 * width)) hi hc
    (by rw [hhead]; exact sourceCell_bound source base width i hindex)
    (by rw [hhead, forward_position]; exact targetCell_bound target targetB base width i hindex)
  have FF : Frames input c cf (distance source target targetB + 1)
      (footprint source target targetB consume base width) := by
    have Fr := (frames_of_contract HF0).mono (G := footprint source target targetB consume base width)
      (by
        intro p hp
        have he : p = targetCell target targetB base i := by
          simpa [cf, startOn, hhead, forward_position] using hp
        exact Or.inl ⟨i, hindex, he⟩)
      (Set.Subset.refl _)
    simpa [Frames, Frame, cf, F, NativeLiteral.live, startOn, NativeLiteral.machine,
      NativeLiteral.position] using Fr
  have hfh : df.workHead = targetCell target targetB base i := by
    simp [df, cf, NativeLiteral.finished, startOn, hhead, forward_position]
  let cb := startOn B df
  let db := NativeLiteral.finished
    (NativeLaneFlagCopy.backward (sourceIndex source) (targetIndex target targetB))
    (distance source target targetB) (if consume then some false else none) cb
  have HB0 := NativeLiteral.firstExit
    (NativeLaneFlagCopy.backward (sourceIndex source) (targetIndex target targetB))
    (distance source target targetB) (if consume then some false else none) input cb hi hc
  have HB : FirstExit (B.step input) (fun _ _ => True) {d | d.state = none}
      cb db (distance source target targetB + 1) := by
    simpa [B, cb, db, NativeLiteral.live, startOn, NativeLiteral.machine,
      NativeLiteral.position] using forget HB0
  have VB := NativeLaneFlagCopy.literal_visits
    (NativeLaneFlagCopy.backward (sourceIndex source) (targetIndex target targetB))
    (distance source target targetB) (if consume then some false else none) input df
    (base + (lanes + 1) * (7 + 3 * width)) hi hc
    (by rw [hfh]; exact targetCell_bound target targetB base width i hindex)
    (by rw [hfh, backward_position]; exact sourceCell_bound source base width i hindex)
  have FB : Frames input df cb (distance source target targetB + 1)
      (footprint source target targetB consume base width) := by
    cases consume with
    | false =>
      exact (NativeLaneFlagCopy.literal_none_frames
        (NativeLaneFlagCopy.backward (sourceIndex source) (targetIndex target targetB))
        (distance source target targetB) input df hi hc).mono (by simp) (Set.Subset.refl _)
    | true =>
      have Fr := (frames_of_contract HB0).mono (G := footprint source target targetB true base width)
        (by
          intro p hp
          have he : p = sourceCell source base i := by
            simpa [cb, startOn, hfh, backward_position] using hp
          exact Or.inr ⟨rfl,i,hindex,he⟩)
        (Set.Subset.refl _)
      simpa [Frames, Frame, cb, B, NativeLiteral.live, startOn, NativeLiteral.machine,
        NativeLiteral.position] using Fr
  have H := seq F B input c df db (distance source target targetB + 1)
    (distance source target targetB + 1) HF HB
  have V := visits_seq F B input c df db (distance source target targetB + 1)
    (distance source target targetB + 1) (base + (lanes + 1) * (7 + 3 * width)) HF HB VF VB
  have Fr := frames_seq F B input c df db (distance source target targetB + 1)
    (distance source target targetB + 1) (footprint source target targetB consume base width) HF HB FF FB
  refine ⟨Sequential.rightConfig F B db, ?_, ?_, ?_, ?_, ?_, ⟨rfl,rfl,rfl,rfl⟩⟩
  · simpa only [bitArm, F, B, show distance source target targetB + 1 +
      (distance source target targetB + 1) = 2 * distance source target targetB + 2 by omega] using H
  · simpa only [bitArm, F, B, show distance source target targetB + 1 +
      (distance source target targetB + 1) = 2 * distance source target targetB + 2 by omega] using V
  · simpa only [bitArm, F, B, show distance source target targetB + 1 +
      (distance source target targetB + 1) = 2 * distance source target targetB + 2 by omega] using Fr
  · change db.workHead = _
    simp [db, cb, NativeLiteral.finished, startOn, hfh, backward_position]
  · change db.work = _
    cases consume <;>
      simp [db, cb, df, cf, NativeLiteral.finished, startOn, Function.update_eq_self,
        hhead, hfh, forward_position, backward_position]

theorem bitHop_exec {N : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (targetB consume : Bool) (input : List Bool) (c : Config N) (base width i : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = sourceCell source base i) (hindex : i < width) :
    ∃ d : Config (bitHop source target targetB consume),
      FirstExit ((bitHop source target targetB consume).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * (7 + 3 * width) ∧
          Frame (footprint source target targetB consume base width) c e)
        {d | d.state = none} (startOn (bitHop source target targetB consume) c) d
        (2 * distance source target targetB + 3) ∧
      d.workHead = sourceCell source base i ∧
      d.work = (if consume then
        Function.update (Function.update c.work (targetCell target targetB base i)
          (c.work (sourceCell source base i))) (sourceCell source base i) false
        else Function.update c.work (targetCell target targetB base i) (c.work (sourceCell source base i))) ∧
      SameIO c d := by
  let A := bitArm source target targetB consume true
  let B := bitArm source target targetB consume false
  cases hb : c.work (sourceCell source base i) with
  | true =>
    obtain ⟨da, HA, VA, FA, hah, haw, haIO⟩ := bitArm_exec source target targetB consume input c base width i true hi hc hhead hindex
    have HE := branch_true A B input c da (2 * distance source target targetB + 2) (by rw [hhead,hb]) hi hc HA
    have VE := visits_branch_true A B input c da (2 * distance source target targetB + 2)
      (base + (lanes + 1) * (7 + 3 * width)) (by rw [hhead,hb]) hi hc HA
      (by rw [hhead]; exact sourceCell_bound source base width i hindex) VA
    have FE := frames_branch_true A B input c da (2 * distance source target targetB + 2)
      (footprint source target targetB consume base width) (by rw [hhead,hb]) hi hc HA FA
    let d := Branch.leftConfig A B da
    have H : FirstExit ((bitHop source target targetB consume).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * (7 + 3 * width) ∧
          Frame (footprint source target targetB consume base width) c e)
        {d | d.state = none} (startOn (bitHop source target targetB consume) c) d
        (1 + (2 * distance source target targetB + 2)) :=
      { result := HE.result
        during := fun u hu e he => ⟨VE u hu e he, FE u hu e he⟩
        exit_mem := HE.exit_mem
        cut := HE.cut }
    refine ⟨d, ?_, hah, ?_, haIO⟩
    · simpa only [show 1 + (2 * distance source target targetB + 2) = 2 * distance source target targetB + 3 by omega] using H
    · change da.work = _
      simpa only [hb] using haw
  | false =>
    obtain ⟨da, HA, VA, FA, hah, haw, haIO⟩ := bitArm_exec source target targetB consume input c base width i false hi hc hhead hindex
    have HE := branch_false A B input c da (2 * distance source target targetB + 2) (by rw [hhead,hb]) hi hc HA
    have VE := visits_branch_false A B input c da (2 * distance source target targetB + 2)
      (base + (lanes + 1) * (7 + 3 * width)) (by rw [hhead,hb]) hi hc HA
      (by rw [hhead]; exact sourceCell_bound source base width i hindex) VA
    have FE := frames_branch_false A B input c da (2 * distance source target targetB + 2)
      (footprint source target targetB consume base width) (by rw [hhead,hb]) hi hc HA FA
    let d := Branch.rightConfig A B da
    have H : FirstExit ((bitHop source target targetB consume).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * (7 + 3 * width) ∧
          Frame (footprint source target targetB consume base width) c e)
        {d | d.state = none} (startOn (bitHop source target targetB consume) c) d
        (1 + (2 * distance source target targetB + 2)) :=
      { result := HE.result
        during := fun u hu e he => ⟨VE u hu e he, FE u hu e he⟩
        exit_mem := HE.exit_mem
        cut := HE.cut }
    refine ⟨d, ?_, hah, ?_, haIO⟩
    · simpa only [show 1 + (2 * distance source target targetB + 2) = 2 * distance source target targetB + 3 by omega] using H
    · change da.work = _
      simpa only [hb] using haw

end CatalyticTreeEval.Contracts.NativeLaneWordTransfer
end

/- Proof source: Solutions.CatalyticTreeEvaluation.WhileFlagLaws -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WhileFlag

open CatalyticMatching.General

theorem step_body (A : Machine) (input : List Bool) (c : Configuration A)
    (live : c.state ≠ none) :
    (machine A).step input (bodyConfig A c) = (A.step input c).map (bodyConfig A) := by
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases hs : state with
    | none => exact False.elim (live hs)
    | some q =>
      simp only [Machine.step, bodyConfig, machine, bodyState, Equiv.symm_apply_apply,
        Option.elim_some, bodyInstruction]
      try dsimp only
      split_ifs <;> simp_all [bodyConfig]

theorem body_halt (A : Machine) (c : Configuration A) (halt : c.state = none) :
    bodyConfig A c = gateConfig A c := by
  cases c
  cases halt
  rfl

theorem step_enter (A : Machine) (input : List Bool) (c : Configuration A)
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    (machine A).step input (gateConfig A c) = some (bodyConfig A (startBody A c)) := by
  cases c
  simp_all [Machine.step, gateConfig, machine, gateState, gateInstruction,
    startBody, bodyConfig, Move.apply, Function.update_eq_self]

theorem step_exit (A : Machine) (input : List Bool) (c : Configuration A)
    (flag : c.work c.workHead = false)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    (machine A).step input (gateConfig A c) = some (haltConfig A c) := by
  cases c
  simp_all [Machine.step, gateConfig, haltConfig, machine, gateState, gateInstruction,
    Move.apply, Function.update_eq_self]

theorem run_body_prefix (A : Machine) (input : List Bool) (c : Configuration A)
    (T : ℕ)
    (live : ∀ u < T, ∀ d, runFrom (A.step input) c u = some d → d.state ≠ none) :
    ∀ u ≤ T, runFrom ((machine A).step input) (bodyConfig A c) u =
      (runFrom (A.step input) c u).map (bodyConfig A) := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
      intro hu
      rw [runFrom_succ, runFrom_succ, ih (by omega)]
      cases hr : runFrom (A.step input) c u with
      | none => rfl
      | some d => simpa using step_body A input d (live u (by omega) d hr)

/-- A loop phase is one real dispatch followed by the body's exact first-exit
execution. Return is folded into the body's halting transition. -/
theorem run_phase (A : Machine) (input : List Bool) (c a : Configuration A)
    {I : ℕ → Configuration A → Prop} {t : ℕ}
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (body : FirstExit (A.step input) I {d | d.state = none} (startBody A c) a t) :
    runFrom ((machine A).step input) (gateConfig A c) (1 + t) =
      some (gateConfig A a) := by
  rw [runFrom_add]
  simp only [runFrom_succ, runFrom_zero, Option.bind_some]
  rw [step_enter A input c flag hi hc]
  have H := run_body_prefix A input (startBody A c) t
    (fun u hu d hd => body.cut u hu d hd) t le_rfl
  simpa only [Option.bind_some, body.result, Option.map_some,
    body_halt A a body.exit_mem] using H

/-- All intermediate configurations, not only the endpoint, inherit the body's
resource invariant. The dispatch configuration is checked separately. -/
theorem framed_phase (A : Machine) (input : List Bool) (c a : Configuration A)
    {IA : ℕ → Configuration A → Prop} {I : ℕ → Configuration (machine A) → Prop} {t : ℕ}
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (body : FirstExit (A.step input) IA {d | d.state = none} (startBody A c) a t)
    (entry : I 0 (gateConfig A c))
    (lift : ∀ u ≤ t, ∀ d, IA u d → I (1 + u) (bodyConfig A d)) :
    Segment ((machine A).step input) I (gateConfig A c) (gateConfig A a) (1 + t) where
  result := run_phase A input c a flag hi hc body
  during u hu d hd := by
    cases u with
    | zero =>
        have heq : gateConfig A c = d := by simpa only [runFrom_zero, Option.some.injEq] using hd
        simpa only [← heq] using entry
    | succ u =>
        rw [show u + 1 = 1 + u by omega, runFrom_add] at hd
        simp only [runFrom_succ, runFrom_zero, Option.bind_some] at hd
        rw [step_enter A input c flag hi hc] at hd
        simp only [Option.bind_some] at hd
        rw [run_body_prefix A input (startBody A c) t
          (fun v hv d hd => body.cut v hv d hd) u (by omega)] at hd
        cases hr : runFrom (A.step input) (startBody A c) u with
        | none => simp [hr] at hd
        | some p =>
            have heq : bodyConfig A p = d := by simpa [hr] using hd
            rw [← heq, show u + 1 = 1 + u by omega]
            exact lift u (by omega) p (body.during u (by omega) p hr)

theorem run_iterations (A : Machine) (input : List Bool) (c : ℕ → Configuration A)
    (time : ℕ → ℕ) (inv : ℕ → ℕ → Configuration A → Prop) (n : ℕ)
    (flags : ∀ i < n, (c i).work (c i).workHead = true)
    (inputs : ∀ i < n, (c i).inputHead ≤ input.length + 1)
    (catalysts : ∀ i < n, (c i).catalystHead ≤ (c i).catalyst.length)
    (bodies : ∀ i < n, FirstExit (A.step input) (inv i) {d | d.state = none}
      (startBody A (c i)) (c (i + 1)) (time i)) :
    runFrom ((machine A).step input) (gateConfig A (c 0)) (elapsed time n) =
      some (gateConfig A (c n)) := by
  induction n with
  | zero => simp [elapsed]
  | succ n ih =>
      have H := ih (fun i hi => flags i (by omega)) (fun i hi => inputs i (by omega))
        (fun i hi => catalysts i (by omega)) (fun i hi => bodies i (by omega))
      simp only [elapsed, Finset.sum_range_succ] at *
      rw [runFrom_add, H]
      exact run_phase A input (c n) (c (n + 1)) (flags n (by omega))
        (inputs n (by omega)) (catalysts n (by omega)) (bodies n (by omega))

theorem run_loop (A : Machine) (input : List Bool) (c : ℕ → Configuration A)
    (time : ℕ → ℕ) (inv : ℕ → ℕ → Configuration A → Prop) (n : ℕ)
    (flags : ∀ i < n, (c i).work (c i).workHead = true)
    (inputs : ∀ i ≤ n, (c i).inputHead ≤ input.length + 1)
    (catalysts : ∀ i ≤ n, (c i).catalystHead ≤ (c i).catalyst.length)
    (bodies : ∀ i < n, FirstExit (A.step input) (inv i) {d | d.state = none}
      (startBody A (c i)) (c (i + 1)) (time i))
    (done : (c n).work (c n).workHead = false) :
    runFrom ((machine A).step input) (gateConfig A (c 0)) (elapsed time n + 1) =
      some (haltConfig A (c n)) := by
  rw [runFrom_succ, run_iterations A input c time inv n flags
    (fun i hi => inputs i (by omega)) (fun i hi => catalysts i (by omega)) bodies]
  exact step_exit A input (c n) done (inputs n le_rfl) (catalysts n le_rfl)

/-- Once each concrete phase has supplied its trajectory invariant, bounded
iteration preserves the same global invariant with its exact time offset. -/
theorem framed_iterations (A : Machine) (input : List Bool) (c : ℕ → Configuration A)
    (time : ℕ → ℕ) (n : ℕ) (I : ℕ → Configuration (machine A) → Prop)
    (entry : I 0 (gateConfig A (c 0)))
    (phases : ∀ i < n, Segment ((machine A).step input)
      (fun u d => I (elapsed time i + u) d)
      (gateConfig A (c i)) (gateConfig A (c (i + 1))) (1 + time i)) :
    Segment ((machine A).step input) I
      (gateConfig A (c 0)) (gateConfig A (c n)) (elapsed time n) := by
  induction n with
  | zero =>
      refine ⟨rfl, ?_⟩
      intro u hu d hd
      have heq : u = 0 := by simpa [elapsed] using hu
      subst u
      have hd' : gateConfig A (c 0) = d := by
        simpa only [runFrom_zero, Option.some.injEq] using hd
      simpa only [← hd'] using entry
  | succ n ih =>
      have H := ih (fun i hi => phases i (by omega))
      have elapsed_succ : elapsed time (n + 1) = elapsed time n + (1 + time n) := by
        simp [elapsed, Finset.sum_range_succ]
      rw [elapsed_succ]
      exact H.trans (phases n (by omega)) (fun _ _ _ h => h) (fun _ _ _ h => h)

theorem framed_loop (A : Machine) (input : List Bool) (c : ℕ → Configuration A)
    (time : ℕ → ℕ) (n : ℕ) (I : ℕ → Configuration (machine A) → Prop)
    (entry : I 0 (gateConfig A (c 0)))
    (phases : ∀ i < n, Segment ((machine A).step input)
      (fun u d => I (elapsed time i + u) d)
      (gateConfig A (c i)) (gateConfig A (c (i + 1))) (1 + time i))
    (done : (c n).work (c n).workHead = false)
    (hi : (c n).inputHead ≤ input.length + 1)
    (hc : (c n).catalystHead ≤ (c n).catalyst.length)
    (exit : I (elapsed time n + 1) (haltConfig A (c n))) :
    Segment ((machine A).step input) I
      (gateConfig A (c 0)) (haltConfig A (c n)) (elapsed time n + 1) := by
  have H := framed_iterations A input c time n I entry phases
  have last : Segment ((machine A).step input) (fun u d => I (elapsed time n + u) d)
      (gateConfig A (c n)) (haltConfig A (c n)) 1 :=
    Segment.single (step_exit A input (c n) done hi hc)
      (by simpa using H.during (elapsed time n) le_rfl _ H.result) exit
  exact H.trans last (fun _ _ _ h => h) (fun _ _ _ h => h)

/-- Throughout the body phases the controller and embedded body states are
live, including their handoff endpoints. -/
theorem live_iterations (A : Machine) (input : List Bool) (c : ℕ → Configuration A)
    (time : ℕ → ℕ) (inv : ℕ → ℕ → Configuration A → Prop) (n : ℕ)
    (flags : ∀ i < n, (c i).work (c i).workHead = true)
    (inputs : ∀ i < n, (c i).inputHead ≤ input.length + 1)
    (catalysts : ∀ i < n, (c i).catalystHead ≤ (c i).catalyst.length)
    (bodies : ∀ i < n, FirstExit (A.step input) (inv i) {d | d.state = none}
      (startBody A (c i)) (c (i + 1)) (time i)) :
    Segment ((machine A).step input) (fun _ d => d.state ≠ none)
      (gateConfig A (c 0)) (gateConfig A (c n)) (elapsed time n) := by
  apply framed_iterations A input c time n (fun _ d => d.state ≠ none)
  · simp [gateConfig]
  · intro i hi
    apply framed_phase A input (c i) (c (i + 1)) (flags i hi)
      (inputs i hi) (catalysts i hi) (bodies i hi)
    · simp [gateConfig]
    · intro u hu d hd
      simp [bodyConfig]

theorem firstExit_loop (A : Machine) (input : List Bool) (c : ℕ → Configuration A)
    (time : ℕ → ℕ) (inv : ℕ → ℕ → Configuration A → Prop) (n : ℕ)
    (I : ℕ → Configuration (machine A) → Prop)
    (flags : ∀ i < n, (c i).work (c i).workHead = true)
    (inputs : ∀ i < n, (c i).inputHead ≤ input.length + 1)
    (catalysts : ∀ i < n, (c i).catalystHead ≤ (c i).catalyst.length)
    (bodies : ∀ i < n, FirstExit (A.step input) (inv i) {d | d.state = none}
      (startBody A (c i)) (c (i + 1)) (time i))
    (execution : Segment ((machine A).step input) I
      (gateConfig A (c 0)) (haltConfig A (c n)) (elapsed time n + 1)) :
    FirstExit ((machine A).step input) I {d | d.state = none}
      (gateConfig A (c 0)) (haltConfig A (c n)) (elapsed time n + 1) where
  toSegment := execution
  exit_mem := rfl
  cut u hu d hd :=
    (live_iterations A input c time inv n flags inputs catalysts bodies).during
      u (by omega) d hd

end CatalyticTreeEval.Contracts.WhileFlag
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeLaneWordForward -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeLaneWordTransfer

open NativeRoundSupport
open RestoringRound (SameIO)

theorem forwardBody_exec {N : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (targetB consume : Bool) (input : List Bool) (c : Config N) (base width i : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = WorkLanes.address source base (6 + 3 * i)) (hindex : i < width) :
    ∃ d : Config (forwardBody source target targetB consume),
      FirstExit ((forwardBody source target targetB consume).step input) (fun _ _ => True)
        {d | d.state = none} (startOn (forwardBody source target targetB consume) c) d
        (3 * (lanes + 1) + 2 * distance source target targetB + 5) ∧
      Visits input (startOn (forwardBody source target targetB consume) c)
        (3 * (lanes + 1) + 2 * distance source target targetB + 5)
        (base + (lanes + 1) * (7 + 3 * width)) ∧
      Frames input c (startOn (forwardBody source target targetB consume) c)
        (3 * (lanes + 1) + 2 * distance source target targetB + 5)
        (footprint source target targetB consume base width) ∧
      d.workHead = WorkLanes.address source base (6 + 3 * (i + 1)) ∧
      d.work = (if consume then
        Function.update (Function.update c.work (targetCell target targetB base i)
          (c.work (sourceCell source base i))) (sourceCell source base i) false
        else Function.update c.work (targetCell target targetB base i) (c.work (sourceCell source base i))) ∧
      SameIO c d := by
  let S := NativeLiteral.machine .right (lanes + 1) none
  let H := bitHop source target targetB consume
  let E := NativeLiteral.machine .right (2 * (lanes + 1)) none
  let bound := base + (lanes + 1) * (7 + 3 * width)
  let F := footprint source target targetB consume base width
  have hp1 : NativeLiteral.position .right c.workHead (lanes + 1) = sourceCell source base i := by
    rw [NativeLiteral.position_right,hhead]
    change WorkLanes.address source base (6 + 3 * i) + (lanes + 1) = WorkLanes.address source base (7 + 3 * i)
    simpa only [Nat.mul_one,show (6 + 3 * i) + 1 = 7 + 3 * i by omega] using
      (address_add_hop source base (6 + 3 * i) 1).symm
  obtain ⟨ds,HS,hsh,hsw,hsIO⟩ := move_exec .right (lanes + 1) input c (sourceCell source base i) bound hi hc hp1
    (by rw [hhead]; exact tag_bound source base width i (by omega)) (sourceCell_bound source base width i hindex)
  have his : ds.inputHead ≤ input.length + 1 := by rw [hsIO.1]; exact hi
  have hcs : ds.catalystHead ≤ ds.catalyst.length := by rw [hsIO.2.1,hsIO.2.2.1]; exact hc
  obtain ⟨dh,HH,hhh,hhw,hhIO⟩ := bitHop_exec source target targetB consume input ds base width i his hcs hsh hindex
  have hp2 : NativeLiteral.position .right dh.workHead (2 * (lanes + 1)) =
      WorkLanes.address source base (6 + 3 * (i + 1)) := by
    rw [NativeLiteral.position_right,hhh]
    change WorkLanes.address source base (7 + 3 * i) + 2 * (lanes + 1) = _
    have H := address_add_hop source base (7 + 3 * i) 2
    rw [Nat.mul_comm (lanes + 1) 2] at H
    simpa only [show (7 + 3 * i) + 2 = 6 + 3 * (i + 1) by omega] using H.symm
  have hih : dh.inputHead ≤ input.length + 1 := by rw [hhIO.1,hsIO.1]; exact hi
  have hch : dh.catalystHead ≤ dh.catalyst.length := by
    rw [hhIO.2.1,hhIO.2.2.1,hsIO.2.1,hsIO.2.2.1]; exact hc
  obtain ⟨de,HE,heh,hew,heIO⟩ := move_exec .right (2 * (lanes + 1)) input dh
    (WorkLanes.address source base (6 + 3 * (i + 1))) bound hih hch hp2
    (by rw [hhh]; exact sourceCell_bound source base width i hindex)
    (tag_bound source base width (i + 1) (by omega))
  have VS : Visits input (startOn S c) (lanes + 1 + 1) bound := fun u hu e he => (HS.during u hu e he).1
  have FS : Frames input c (startOn S c) (lanes + 1 + 1) F :=
    fun u hu e he => ((HS.during u hu e he).2).mono (by simp) (by simp)
  have VH : Visits input (startOn H ds) (2 * distance source target targetB + 3) bound := fun u hu e he => (HH.during u hu e he).1
  have FH : Frames input ds (startOn H ds) (2 * distance source target targetB + 3) F := fun u hu e he => (HH.during u hu e he).2
  have VE : Visits input (startOn E dh) (2 * (lanes + 1) + 1) bound := fun u hu e he => (HE.during u hu e he).1
  have FE : Frames input dh (startOn E dh) (2 * (lanes + 1) + 1) F :=
    fun u hu e he => ((HE.during u hu e he).2).mono (by simp) (by simp)
  have HHE := seq H E input ds dh de (2 * distance source target targetB + 3)
    (2 * (lanes + 1) + 1) (forget HH) (forget HE)
  have VHE := visits_seq H E input ds dh de (2 * distance source target targetB + 3)
    (2 * (lanes + 1) + 1) bound (forget HH) (forget HE) VH VE
  have FHE := frames_seq H E input ds dh de (2 * distance source target targetB + 3)
    (2 * (lanes + 1) + 1) F (forget HH) (forget HE) FH FE
  have Hfull := seq S (Sequential.machine H E) input c ds (Sequential.rightConfig H E de)
    (lanes + 1 + 1) (2 * distance source target targetB + 3 + (2 * (lanes + 1) + 1)) (forget HS) HHE
  have Vfull := visits_seq S (Sequential.machine H E) input c ds (Sequential.rightConfig H E de)
    (lanes + 1 + 1) (2 * distance source target targetB + 3 + (2 * (lanes + 1) + 1)) bound (forget HS) HHE VS VHE
  have Ffull := frames_seq S (Sequential.machine H E) input c ds (Sequential.rightConfig H E de)
    (lanes + 1 + 1) (2 * distance source target targetB + 3 + (2 * (lanes + 1) + 1)) F (forget HS) HHE FS FHE
  let d := Sequential.rightConfig S (Sequential.machine H E) (Sequential.rightConfig H E de)
  have ht : (lanes + 1 + 1) + (2 * distance source target targetB + 3 + (2 * (lanes + 1) + 1)) =
      3 * (lanes + 1) + 2 * distance source target targetB + 5 := by omega
  refine ⟨d,?_,?_,?_,heh,?_,sameIO_trans hsIO (sameIO_trans hhIO heIO)⟩
  · simpa only [forwardBody,S,H,E,ht] using Hfull
  · simpa only [forwardBody,S,H,E,ht] using Vfull
  · simpa only [forwardBody,S,H,E,ht] using Ffull
  · change de.work = _
    rw [hew,hhw,hsw]

def forwardPhase {N : Main.Machine} {lanes : ℕ} (source target : Fin lanes) (targetB consume : Bool)
    (base : ℕ) (c : Config N) (n : ℕ) : Config (forwardBody source target targetB consume) :=
  {c with
    state := none
    workHead := WorkLanes.address source base (6 + 3 * n)
    work := prefixWork source target targetB consume base c.work n}

theorem config_eq {M : Main.Machine} (a b : Config M)
    (hs : a.state = b.state) (hi : a.inputHead = b.inputHead) (hw : a.workHead = b.workHead)
    (hc : a.catalystHead = b.catalystHead) (hwork : a.work = b.work)
    (hcat : a.catalyst = b.catalyst) (hout : a.output = b.output) : a = b := by
  cases a
  cases b
  simp_all

theorem forwardPhase_frame {N M : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (targetB consume : Bool) (base width n : ℕ) (c : Config N) (hn : n ≤ width)
    (e : Config M) (hw : e.work = (forwardPhase source target targetB consume base c n).work)
    (hc : e.catalyst = c.catalyst) : Frame (footprint source target targetB consume base width) c e := by
  refine ⟨?_,by rw [hc],fun p hp => by rw [hc]⟩
  intro p hp
  rw [hw]
  exact prefixWork_outside source target targetB consume base width c.work n hn p hp

theorem forwardScan_exec {N : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (targetB consume : Bool) (input : List Bool) (c : Config N) (base width : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = WorkLanes.address source base 6) (hne : source ≠ target)
    (htags : ∀ i < width, c.work (WorkLanes.address source base (6 + 3 * i)) = true)
    (hstop : c.work (WorkLanes.address source base (6 + 3 * width)) = false) :
    ∃ d : Config (forwardScan source target targetB consume),
      FirstExit ((forwardScan source target targetB consume).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * (7 + 3 * width) ∧
          Frame (footprint source target targetB consume base width) c e)
        {d | d.state = none} (startOn (forwardScan source target targetB consume) c) d
        (width * (3 * (lanes + 1) + 2 * distance source target targetB + 6) + 1) ∧
      d.workHead = WorkLanes.address source base (6 + 3 * width) ∧
      d.work = prefixWork source target targetB consume base c.work width ∧ SameIO c d := by
  let A := forwardBody source target targetB consume
  let phase := forwardPhase source target targetB consume base c
  let bodyTime := 3 * (lanes + 1) + 2 * distance source target targetB + 5
  let time : ℕ → ℕ := fun _ => bodyTime
  let F := footprint source target targetB consume base width
  let bound := base + (lanes + 1) * (7 + 3 * width)
  let IA := fun (n : ℕ) (_ : ℕ) (e : Config A) => e.workHead < bound ∧ Frame F (phase n) e
  have bodies : ∀ n < width, FirstExit (A.step input) (IA n) {e | e.state = none}
      (WhileFlag.startBody A (phase n)) (phase (n + 1)) (time n) := by
    intro n hn
    obtain ⟨d,H,V,Fr,hdh,hdw,hdIO⟩ := forwardBody_exec source target targetB consume input (phase n) base width n hi hc rfl hn
    have hbit : (phase n).work (sourceCell source base n) = c.work (sourceCell source base n) :=
      prefixWork_unprocessed_source source target targetB consume base n n c.work hne le_rfl
    have hdw' : d.work = (phase (n + 1)).work := by
      rw [hdw,hbit]
      rfl
    have heq : d = phase (n + 1) := config_eq d _ H.exit_mem hdIO.1 hdh hdIO.2.1 hdw' hdIO.2.2.1 hdIO.2.2.2
    subst d
    exact
      { result := H.result
        during := fun u hu e he => ⟨V u hu e he,Fr u hu e he⟩
        exit_mem := H.exit_mem
        cut := H.cut }
  have phaseTag : ∀ n ≤ width,
      (phase n).work (WorkLanes.address source base (6 + 3 * n)) =
        c.work (WorkLanes.address source base (6 + 3 * n)) := by
    intro n hn
    exact prefixWork_outside source target targetB consume base width c.work n hn _
      (tag_outside source target source targetB consume base width n)
  have flags : ∀ n < width, (phase n).work (phase n).workHead = true := by
    intro n hn
    exact (phaseTag n (by omega)).trans (htags n hn)
  have inputs : ∀ n ≤ width, (phase n).inputHead ≤ input.length + 1 := fun _ _ => hi
  have catalysts : ∀ n ≤ width, (phase n).catalystHead ≤ (phase n).catalyst.length := fun _ _ => hc
  let I := fun (_ : ℕ) (e : Config (WhileFlag.machine A)) => e.workHead < bound ∧ Frame F c e
  have gate : ∀ n ≤ width, ∀ u, I u (WhileFlag.gateConfig A (phase n)) := by
    intro n hn u
    exact ⟨tag_bound source base width n hn,
      forwardPhase_frame source target targetB consume base width n c hn _ rfl rfl⟩
  have phases : ∀ n < width, Segment ((WhileFlag.machine A).step input)
      (fun u e => I (WhileFlag.elapsed time n + u) e)
      (WhileFlag.gateConfig A (phase n)) (WhileFlag.gateConfig A (phase (n + 1))) (1 + time n) := by
    intro n hn
    apply WhileFlag.framed_phase A input (phase n) (phase (n + 1)) (flags n hn)
      (inputs n (by omega)) (catalysts n (by omega)) (bodies n hn)
    · exact gate n (by omega) 0
    · intro u hu e he
      have Fcp : Frame F c (phase n) := forwardPhase_frame source target targetB consume base width n c (by omega) _ rfl rfl
      exact ⟨he.1,Fcp.trans he.2⟩
  have done : (phase width).work (phase width).workHead = false :=
    (phaseTag width le_rfl).trans hstop
  have exitInv : I (WhileFlag.elapsed time width + 1) (WhileFlag.haltConfig A (phase width)) :=
    ⟨tag_bound source base width width le_rfl,
      forwardPhase_frame source target targetB consume base width width c le_rfl _ rfl rfl⟩
  have execution := WhileFlag.framed_loop A input phase time width I (gate 0 (by omega) 0) phases done
    (inputs width le_rfl) (catalysts width le_rfl) exitInv
  have H := WhileFlag.firstExit_loop A input phase time IA width I flags
    (fun n hn => inputs n (by omega)) (fun n hn => catalysts n (by omega)) bodies execution
  have ht : WhileFlag.elapsed time width = width * (3 * (lanes + 1) + 2 * distance source target targetB + 6) := by
    simp [WhileFlag.elapsed,time,bodyTime,show 1 + (3 * (lanes + 1) + 2 * distance source target targetB + 5) =
      3 * (lanes + 1) + 2 * distance source target targetB + 6 by omega]
  refine ⟨WhileFlag.haltConfig A (phase width),?_,rfl,rfl,⟨rfl,rfl,rfl,rfl⟩⟩
  simpa [forwardScan,phase,forwardPhase,A,WhileFlag.gateConfig,WhileFlag.machine,startOn,prefixWork,hhead,ht,I,F,bound] using H

end CatalyticTreeEval.Contracts.NativeLaneWordTransfer
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeLaneWordRewind -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeLaneWordTransfer

open NativeRoundSupport
open RestoringRound (SameIO)

def rewindPhase {N : Main.Machine} {lanes : ℕ} (source : Fin lanes) (base width : ℕ)
    (c : Config N) (n : ℕ) : Config (backStep lanes) :=
  {c with state := none,workHead := WorkLanes.address source base (3 + 3 * (width - n))}

theorem backScan_exec {N : Main.Machine} {lanes : ℕ} (source : Fin lanes)
    (input : List Bool) (c : Config N) (base width : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = WorkLanes.address source base (3 + 3 * width))
    (htags : ∀ i < width, c.work (WorkLanes.address source base (6 + 3 * i)) = true)
    (hmarker : c.work (WorkLanes.address source base 3) = false) :
    ∃ d : Config (WhileFlag.machine (backStep lanes)),
      FirstExit ((WhileFlag.machine (backStep lanes)).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * (7 + 3 * width) ∧ Frame ⟨∅,∅⟩ c e)
        {d | d.state = none} (startOn (WhileFlag.machine (backStep lanes)) c) d
        (width * (3 * (lanes + 1) + 2) + 1) ∧
      d.workHead = WorkLanes.address source base 3 ∧ d.work = c.work ∧ SameIO c d := by
  let A := backStep lanes
  let phase := rewindPhase source base width c
  let time : ℕ → ℕ := fun _ => 3 * (lanes + 1) + 1
  let bound := base + (lanes + 1) * (7 + 3 * width)
  let IA := fun (n : ℕ) (_ : ℕ) (e : Config A) => e.workHead < bound ∧ Frame ⟨∅,∅⟩ (phase n) e
  have phaseBound : ∀ n, (phase n).workHead < bound := by
    intro n
    exact WorkLanes.address_lt_prefix source base _ _ (by omega)
  have bodies : ∀ n < width, FirstExit (A.step input) (IA n) {e | e.state = none}
      (WhileFlag.startBody A (phase n)) (phase (n + 1)) (time n) := by
    intro n hn
    have hp : NativeLiteral.position .left (phase n).workHead (3 * (lanes + 1)) =
        WorkLanes.address source base (3 + 3 * (width - (n + 1))) := by
      rw [NativeLiteral.position_left]
      change WorkLanes.address source base (3 + 3 * (width - n)) - 3 * (lanes + 1) = _
      rw [show 3 + 3 * (width - n) = (3 + 3 * (width - (n + 1))) + 3 by omega,
        address_add_hop source base (3 + 3 * (width - (n + 1))) 3,Nat.mul_comm (lanes + 1) 3,
        Nat.add_sub_cancel]
    obtain ⟨d,H,hdh,hdw,hdIO⟩ := move_exec .left (3 * (lanes + 1)) input (phase n)
      (WorkLanes.address source base (3 + 3 * (width - (n + 1)))) bound hi hc hp (phaseBound n) (phaseBound (n + 1))
    have heq : d = phase (n + 1) := config_eq d _ H.exit_mem hdIO.1 hdh hdIO.2.1 hdw hdIO.2.2.1 hdIO.2.2.2
    subst d
    exact H
  have flags : ∀ n < width, (phase n).work (phase n).workHead = true := by
    intro n hn
    change c.work (WorkLanes.address source base (3 + 3 * (width - n))) = true
    rw [show 3 + 3 * (width - n) = 6 + 3 * (width - n - 1) by omega]
    exact htags _ (by omega)
  have inputs : ∀ n ≤ width, (phase n).inputHead ≤ input.length + 1 := fun _ _ => hi
  have catalysts : ∀ n ≤ width, (phase n).catalystHead ≤ (phase n).catalyst.length := fun _ _ => hc
  let I := fun (_ : ℕ) (e : Config (WhileFlag.machine A)) => e.workHead < bound ∧ Frame ⟨∅,∅⟩ c e
  have gate : ∀ n u, I u (WhileFlag.gateConfig A (phase n)) := by
    intro n u
    exact ⟨phaseBound n,⟨fun _ _ => rfl,rfl,fun _ _ => rfl⟩⟩
  have phases : ∀ n < width, Segment ((WhileFlag.machine A).step input)
      (fun u e => I (WhileFlag.elapsed time n + u) e)
      (WhileFlag.gateConfig A (phase n)) (WhileFlag.gateConfig A (phase (n + 1))) (1 + time n) := by
    intro n hn
    apply WhileFlag.framed_phase A input (phase n) (phase (n + 1)) (flags n hn)
      (inputs n (by omega)) (catalysts n (by omega)) (bodies n hn)
    · exact gate n 0
    · intro u hu e he
      exact ⟨he.1,he.2⟩
  have done : (phase width).work (phase width).workHead = false := by
    simpa [phase,rewindPhase] using hmarker
  have exitInv : I (WhileFlag.elapsed time width + 1) (WhileFlag.haltConfig A (phase width)) :=
    ⟨phaseBound width,⟨fun _ _ => rfl,rfl,fun _ _ => rfl⟩⟩
  have execution := WhileFlag.framed_loop A input phase time width I (gate 0 0) phases done
    (inputs width le_rfl) (catalysts width le_rfl) exitInv
  have H := WhileFlag.firstExit_loop A input phase time IA width I flags
    (fun n hn => inputs n (by omega)) (fun n hn => catalysts n (by omega)) bodies execution
  have ht : WhileFlag.elapsed time width = width * (3 * (lanes + 1) + 2) := by
    simp [WhileFlag.elapsed,time,show 1 + (3 * (lanes + 1) + 1) = 3 * (lanes + 1) + 2 by omega]
  refine ⟨WhileFlag.haltConfig A (phase width),?_,?_,rfl,⟨rfl,rfl,rfl,rfl⟩⟩
  · simpa [phase,rewindPhase,A,WhileFlag.gateConfig,WhileFlag.machine,startOn,hhead,ht,I,bound] using H
  · simp [phase,rewindPhase,WhileFlag.haltConfig]

theorem rewind_exec {N : Main.Machine} {lanes : ℕ} (source : Fin lanes)
    (input : List Bool) (c : Config N) (base width : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = WorkLanes.address source base (6 + 3 * width))
    (htags : ∀ i < width, c.work (WorkLanes.address source base (6 + 3 * i)) = true)
    (hmarker : c.work (WorkLanes.address source base 3) = false) :
    ∃ d : Config (rewind lanes),
      FirstExit ((rewind lanes).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * (7 + 3 * width) ∧ Frame ⟨∅,∅⟩ c e)
        {d | d.state = none} (startOn (rewind lanes) c) d
        (width * (3 * (lanes + 1) + 2) + 6 * (lanes + 1) + 3) ∧
      d.workHead = WorkLanes.address source base 0 ∧ d.work = c.work ∧ SameIO c d := by
  let A := backStep lanes
  let B := WhileFlag.machine A
  let bound := base + (lanes + 1) * (7 + 3 * width)
  have hp1 : NativeLiteral.position .left c.workHead (3 * (lanes + 1)) =
      WorkLanes.address source base (3 + 3 * width) := by
    rw [NativeLiteral.position_left,hhead,show 6 + 3 * width = (3 + 3 * width) + 3 by omega,
      address_add_hop source base (3 + 3 * width) 3,Nat.mul_comm (lanes + 1) 3,Nat.add_sub_cancel]
  obtain ⟨d1,H1,hd1h,hd1w,hd1IO⟩ := move_exec .left (3 * (lanes + 1)) input c
    (WorkLanes.address source base (3 + 3 * width)) bound hi hc hp1 (by rw [hhead];exact tag_bound source base width width le_rfl)
    (WorkLanes.address_lt_prefix source base _ _ (by omega))
  have hi1 : d1.inputHead ≤ input.length + 1 := by rw [hd1IO.1];exact hi
  have hc1 : d1.catalystHead ≤ d1.catalyst.length := by rw [hd1IO.2.1,hd1IO.2.2.1];exact hc
  obtain ⟨d2,H2,hd2h,hd2w,hd2IO⟩ := backScan_exec source input d1 base width hi1 hc1 hd1h
    (by intro i hiw;rw [hd1w];exact htags i hiw) (by rw [hd1w];exact hmarker)
  have hp3 : NativeLiteral.position .left d2.workHead (3 * (lanes + 1)) = WorkLanes.address source base 0 := by
    rw [NativeLiteral.position_left,hd2h]
    have H := address_add_hop source base 0 3
    simp only [Nat.zero_add,Nat.mul_comm (lanes + 1) 3] at H
    rw [H,Nat.add_sub_cancel]
  have hi2 : d2.inputHead ≤ input.length + 1 := by rw [hd2IO.1,hd1IO.1];exact hi
  have hc2 : d2.catalystHead ≤ d2.catalyst.length := by rw [hd2IO.2.1,hd2IO.2.2.1,hd1IO.2.1,hd1IO.2.2.1];exact hc
  obtain ⟨d3,H3,hd3h,hd3w,hd3IO⟩ := move_exec .left (3 * (lanes + 1)) input d2
    (WorkLanes.address source base 0) bound hi2 hc2 hp3 (by rw [hd2h];exact WorkLanes.address_lt_prefix source base _ _ (by omega))
    (WorkLanes.address_lt_prefix source base _ _ (by omega))
  have V1 : Visits input (startOn A c) (3 * (lanes + 1) + 1) bound := fun u hu e he => (H1.during u hu e he).1
  have F1 : Frames input c (startOn A c) (3 * (lanes + 1) + 1) ⟨∅,∅⟩ := fun u hu e he => (H1.during u hu e he).2
  have V2 : Visits input (startOn B d1) (width * (3 * (lanes + 1) + 2) + 1) bound := fun u hu e he => (H2.during u hu e he).1
  have F2 : Frames input d1 (startOn B d1) (width * (3 * (lanes + 1) + 2) + 1) ⟨∅,∅⟩ := fun u hu e he => (H2.during u hu e he).2
  have V3 : Visits input (startOn A d2) (3 * (lanes + 1) + 1) bound := fun u hu e he => (H3.during u hu e he).1
  have F3 : Frames input d2 (startOn A d2) (3 * (lanes + 1) + 1) ⟨∅,∅⟩ := fun u hu e he => (H3.during u hu e he).2
  have H23 := seq B A input d1 d2 d3 (width * (3 * (lanes + 1) + 2) + 1) (3 * (lanes + 1) + 1) (forget H2) (forget H3)
  have V23 := visits_seq B A input d1 d2 d3 (width * (3 * (lanes + 1) + 2) + 1) (3 * (lanes + 1) + 1) bound (forget H2) (forget H3) V2 V3
  have F23 := frames_seq B A input d1 d2 d3 (width * (3 * (lanes + 1) + 2) + 1) (3 * (lanes + 1) + 1) ⟨∅,∅⟩ (forget H2) (forget H3) F2 F3
  have Hfull := seq A (Sequential.machine B A) input c d1 (Sequential.rightConfig B A d3) (3 * (lanes + 1) + 1)
    (width * (3 * (lanes + 1) + 2) + 1 + (3 * (lanes + 1) + 1)) (forget H1) H23
  have Vfull := visits_seq A (Sequential.machine B A) input c d1 (Sequential.rightConfig B A d3) (3 * (lanes + 1) + 1)
    (width * (3 * (lanes + 1) + 2) + 1 + (3 * (lanes + 1) + 1)) bound (forget H1) H23 V1 V23
  have Ffull := frames_seq A (Sequential.machine B A) input c d1 (Sequential.rightConfig B A d3) (3 * (lanes + 1) + 1)
    (width * (3 * (lanes + 1) + 2) + 1 + (3 * (lanes + 1) + 1)) ⟨∅,∅⟩ (forget H1) H23 F1 F23
  let d := Sequential.rightConfig A (Sequential.machine B A) (Sequential.rightConfig B A d3)
  have ht : 3 * (lanes + 1) + 1 + (width * (3 * (lanes + 1) + 2) + 1 + (3 * (lanes + 1) + 1)) =
      width * (3 * (lanes + 1) + 2) + 6 * (lanes + 1) + 3 := by omega
  have H : FirstExit ((rewind lanes).step input)
      (fun _ e => e.workHead < bound ∧ Frame ⟨∅,∅⟩ c e) {d | d.state = none}
      (startOn (rewind lanes) c) d (3 * (lanes + 1) + 1 + (width * (3 * (lanes + 1) + 2) + 1 + (3 * (lanes + 1) + 1))) :=
    { result := Hfull.result
      during := fun u hu e he => ⟨Vfull u hu e he,Ffull u hu e he⟩
      exit_mem := Hfull.exit_mem
      cut := Hfull.cut }
  refine ⟨d,?_,hd3h,?_,sameIO_trans hd1IO (sameIO_trans hd2IO hd3IO)⟩
  · simpa only [ht] using H
  · change d3.work = _
    rw [hd3w,hd2w,hd1w]

end CatalyticTreeEval.Contracts.NativeLaneWordTransfer
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeMarkerSeekPort -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeMarkerSeek

open CatalyticMatching.General
open NativeRoundSupport
open RestoringRound (SameIO)

/-- A marker search can be called from any finite controller, at its actual
physical head. Both endpoint bounds suffice for its whole monotone traversal. -/
theorem seek_exec {N : Main.Machine} (direction : Move) (padding : ℕ)
    (input : List Bool) (c : Config N) (rows target bound : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (position : NativeLiteral.position direction c.workHead (rows * (padding + 1)) = target)
    (hstart : c.workHead < bound) (hend : target < bound)
    (markers : ∀ i < rows,
      c.work (NativeLiteral.position direction c.workHead (i * (padding + 1))) = false)
    (marker : c.work target = true) :
    ∃ d : Config (machine direction padding),
      FirstExit ((machine direction padding).step input)
        (fun _ e => e.workHead < bound ∧ Frame ⟨∅,∅⟩ c e)
        {e | e.state = none} (startOn (machine direction padding) c) d
        (rows * (padding + 1) + 1) ∧
      d.workHead = target ∧ d.work = c.work ∧ SameIO c d := by
  let cc := startOn (machine direction padding) c
  let d := finished direction padding cc rows
  have H0 := firstExit direction padding input cc rows hi hc markers
    (by simpa only [cc, startOn, position] using marker)
  have entry : cursor direction padding cc 0 = cc := by
    simp [cursor, cc, startOn, machine, NativeLiteral.position]
  have H : FirstExit ((machine direction padding).step input)
      (fun _ e => e.workHead < bound ∧ Frame ⟨∅,∅⟩ c e)
      {e | e.state = none} cc d (rows * (padding + 1) + 1) := by
    rw [entry] at H0
    exact { result := H0.result
            during := by
              intro u hu e he
              have hv := H0.during u hu e he
              have hh : e.workHead < max c.workHead target + 1 := by
                simpa only [cc, startOn, position] using hv.1.2.1
              exact ⟨by omega, hv.2⟩
            exit_mem := H0.exit_mem
            cut := H0.cut }
  exact ⟨d, H, by simpa only [d, finished, cc, startOn] using position,
    rfl, ⟨rfl,rfl,rfl,rfl⟩⟩

end CatalyticTreeEval.Contracts.NativeMarkerSeek
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeFramedComposition -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeRoundSupport

/-- Compose actual native exits while retaining the complete work-head and
memory frame for every prefix, including the finite dispatch seam. -/
theorem framed_seq {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (a : Config A) (b : Config B) (s t bound : ℕ) (F : Footprint)
    (HA : FirstExit (A.step input)
      (fun _ e => e.workHead < bound ∧ Frame F c e) {d | d.state = none}
      (startOn A c) a s)
    (HB : FirstExit (B.step input)
      (fun _ e => e.workHead < bound ∧ Frame F a e) {d | d.state = none}
      (startOn B a) b t) :
    FirstExit ((Sequential.machine A B).step input)
      (fun _ e => e.workHead < bound ∧ Frame F c e) {d | d.state = none}
      (startOn (Sequential.machine A B) c) (Sequential.rightConfig A B b) (s+t) := by
  have H := seq A B input c a b s t (forget HA) (forget HB)
  have V := visits_seq A B input c a b s t bound (forget HA) (forget HB)
    (fun u hu e he => (HA.during u hu e he).1)
    (fun u hu e he => (HB.during u hu e he).1)
  have Fr := frames_seq A B input c a b s t F (forget HA) (forget HB)
    (fun u hu e he => (HA.during u hu e he).2)
    (fun u hu e he => (HB.during u hu e he).2)
  exact { result := H.result
          during := fun u hu e he => ⟨V u hu e he, Fr u hu e he⟩
          exit_mem := H.exit_mem
          cut := H.cut }

theorem firstExit_mono {N A : Main.Machine} (input : List Bool)
    (c : Config N) (a d : Config A) (time bound bound' : ℕ) (F G : Footprint)
    (H : FirstExit (A.step input)
      (fun _ e => e.workHead < bound ∧ Frame F c e) {d | d.state = none} a d time)
    (hb : bound ≤ bound') (hw : F.work ⊆ G.work) (hc : F.catalyst ⊆ G.catalyst) :
    FirstExit (A.step input)
      (fun _ e => e.workHead < bound' ∧ Frame G c e) {d | d.state = none} a d time :=
  { result := H.result
    during := fun u hu e he =>
      ⟨lt_of_lt_of_le (H.during u hu e he).1 hb, (H.during u hu e he).2.mono hw hc⟩
    exit_mem := H.exit_mem
    cut := H.cut }

end CatalyticTreeEval.Contracts.NativeRoundSupport
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeInputLocate -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeInputLocate

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

theorem padding_succ (lanes : ℕ) : padding lanes+1=3*(lanes+1):=by
  unfold padding
  omega

/-- Actual read-only input-cursor location. The unique bookmark invariant
supplies only cell values; the finite native search charges every crossed
physical cell. No input or catalyst head is moved. -/
theorem machine_exec {N : Main.Machine} {lanes : ℕ} (bookmark : Fin lanes)
    (input : List Bool) (c : Config N) (base inputHead bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=base+lanes)
    (cursor : ∀ j ≤ inputHead,
      c.work (WorkLanes.address bookmark base (3+3*j))=decide (j=inputHead))
    (hb : WorkLanes.address bookmark base (3+3*inputHead) < bound) :
    ∃ d : Config (machine bookmark),
      FirstExit ((machine bookmark).step input)
        (fun _ e => e.workHead < bound ∧ Frame ⟨∅,∅⟩ c e)
        {e | e.state=none} (startOn (machine bookmark) c) d (time bookmark inputHead) ∧
      d.workHead=WorkLanes.address bookmark base (3+3*inputHead) ∧
      d.work=c.work ∧ SameIO c d := by
  let A:=NativeLiteral.machine .right (entryDistance bookmark) none
  let B:=NativeMarkerSeek.machine .right (padding lanes)
  have hstart : c.workHead < bound:=by
    rw [head]
    dsimp [WorkLanes.address] at hb
    nlinarith [bookmark.isLt,Nat.zero_le ((lanes+1)*inputHead)]
  have hfirst : WorkLanes.address bookmark base 3 < bound:=by
    dsimp [WorkLanes.address] at hb ⊢
    nlinarith [Nat.zero_le ((lanes+1)*inputHead)]
  obtain ⟨a,HA,ah,aw,aIO⟩:=NativeLaneWordTransfer.move_exec .right (entryDistance bookmark) input c
    (WorkLanes.address bookmark base 3) bound hi hc
    (by rw [NativeLiteral.position_right,head];dsimp [entryDistance,WorkLanes.address];omega) hstart hfirst
  have hia : a.inputHead ≤ input.length+1:=by rw [aIO.1];exact hi
  have hca : a.catalystHead ≤ a.catalyst.length:=by rw [aIO.2.1,aIO.2.2.1];exact hc
  have pos (j : ℕ) : NativeLiteral.position .right a.workHead (j*(padding lanes+1))=
      WorkLanes.address bookmark base (3+3*j):=by
    rw [NativeLiteral.position_right,ah,padding_succ]
    dsimp [WorkLanes.address]
    ring
  obtain ⟨b,HB,bh,bw,bIO⟩:=NativeMarkerSeek.seek_exec .right (padding lanes) input a inputHead
    (WorkLanes.address bookmark base (3+3*inputHead)) bound hia hca (pos inputHead)
    (by rw [ah];exact hfirst) hb
    (by intro j hj;rw [pos j,aw,cursor j (by omega)];simp [show j≠inputHead by omega])
    (by rw [aw,cursor inputHead le_rfl];simp)
  have H:=framed_seq A B input c a b _ _ bound ⟨∅,∅⟩ HA HB
  let d:=Sequential.rightConfig A B b
  refine ⟨d,H,bh,?_,sameIO_trans aIO bIO⟩
  change b.work=c.work
  rw [bw,aw]

end CatalyticTreeEval.Contracts.NativeInputLocate
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeLiteralWritePort -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeLiteral

open CatalyticMatching.General
open NativeRoundSupport
open RestoringRound (SameIO)

/-- An actual fixed-distance move followed by one literal write. The write and
the zero-distance case each cost a transition; arbitrary initial tape data stay
unchanged outside the destination cell at every prefix. -/
theorem write_exec {N : Main.Machine} (direction : Move) (moves : ℕ) (bit : Bool)
    (input : List Bool) (c : Config N) (target bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hposition : position direction c.workHead moves = target)
    (hstart : c.workHead < bound) (hend : target < bound) :
    ∃ d : Config (machine direction moves (some bit)),
      FirstExit ((machine direction moves (some bit)).step input)
        (fun _ e => e.workHead < bound ∧ Frame ⟨{target},∅⟩ c e)
        {e | e.state=none} (startOn (machine direction moves (some bit)) c) d
        (moves+1) ∧
      d.workHead=target ∧ d.work=Function.update c.work target bit ∧ SameIO c d := by
  let cc := startOn (machine direction moves (some bit)) c
  let d := finished direction moves (some bit) cc
  have H0 := firstExit direction moves (some bit) input cc hi hc
  have H : FirstExit ((machine direction moves (some bit)).step input)
      (fun _ _ => True) {e | e.state=none} cc d (moves+1) := by
    simpa [cc,d,live,startOn,machine,position] using forget H0
  have V := NativeLaneFlagCopy.literal_visits direction moves (some bit) input c bound hi hc
    hstart (by rw [hposition]; exact hend)
  have F : Frames input c cc (moves+1) ⟨{target},∅⟩ := by
    have HF := frames_of_contract H0
    simpa [Frames,Frame,cc,live,startOn,machine,position,hposition] using HF
  refine ⟨d,?_,?_,?_,⟨rfl,rfl,rfl,rfl⟩⟩
  · exact { result := H.result
            during := fun u hu e he => ⟨V u hu e he,F u hu e he⟩
            exit_mem := H.exit_mem
            cut := H.cut }
  · simpa [d,cc,finished,startOn] using hposition
  · simp [d,cc,finished,startOn,hposition]

end CatalyticTreeEval.Contracts.NativeLiteral
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeInputInspectReply -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeInputInspect

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

theorem write_exec {N : Main.Machine} {lanes : ℕ} (source target : Fin lanes) (bit : Bool)
    (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+source.val) (hb : rowBase+lanes ≤ bound) :
    ∃ d : Config (write source target bit),
      FirstExit ((write source target bit).step input)
        (fun _ e => e.workHead < bound ∧ Frame ⟨{rowBase+target.val},∅⟩ c e)
        {e | e.state=none} (startOn (write source target bit) c) d
        (NativeLaneFlagCopy.distance source target+1) ∧
      d.workHead=rowBase+target.val ∧ d.work=Function.update c.work (rowBase+target.val) bit ∧ SameIO c d := by
  exact NativeLiteral.write_exec (NativeLaneFlagCopy.forward source target)
    (NativeLaneFlagCopy.distance source target) bit input c (rowBase+target.val) bound hi hc
    (by rw [head];exact NativeLaneFlagCopy.forward_position source target rowBase)
    (by rw [head];omega) (by omega)

theorem move_exec {N : Main.Machine} {lanes : ℕ} (source target : Fin lanes)
    (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+source.val) (hb : rowBase+lanes ≤ bound) :
    ∃ d : Config (move source target),
      FirstExit ((move source target).step input)
        (fun _ e => e.workHead < bound ∧ Frame ⟨∅,∅⟩ c e)
        {e | e.state=none} (startOn (move source target) c) d
        (NativeLaneFlagCopy.distance source target+1) ∧
      d.workHead=rowBase+target.val ∧ d.work=c.work ∧ SameIO c d := by
  exact NativeLaneWordTransfer.move_exec (NativeLaneFlagCopy.forward source target)
    (NativeLaneFlagCopy.distance source target) input c (rowBase+target.val) bound hi hc
    (by rw [head];exact NativeLaneFlagCopy.forward_position source target rowBase)
    (by rw [head];omega) (by omega)

/-- Actual local reply materialization. Its location is carried by the real
head and no runtime row enters control. The complete update expression also
specifies the behavior before role-distinctness assumptions are applied. -/
theorem writeReply_exec {N : Main.Machine} {lanes : ℕ} (r : Roles lanes) (source : Fin lanes)
    (reply : Reply) (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+source.val) (hb : rowBase+lanes ≤ bound) :
    ∃ d : Config (writeReply r source reply),
      FirstExit ((writeReply r source reply).step input)
        (fun _ e => e.workHead < bound ∧
          Frame ⟨{rowBase+r.replyOrigin.val,rowBase+r.replyPresent.val,rowBase+r.replyValue.val},∅⟩ c e)
        {e | e.state=none} (startOn (writeReply r source reply) c) d (replyTime r source) ∧
      d.workHead=rowBase+r.replyOrigin.val ∧
      d.work=Function.update (Function.update (Function.update c.work
        (rowBase+r.replyOrigin.val) reply.isOrigin) (rowBase+r.replyPresent.val) reply.isPresent)
        (rowBase+r.replyValue.val) reply.value ∧ SameIO c d := by
  let F : Footprint:=⟨{rowBase+r.replyOrigin.val,rowBase+r.replyPresent.val,rowBase+r.replyValue.val},∅⟩
  let A:=write source r.replyOrigin reply.isOrigin
  let B:=write r.replyOrigin r.replyPresent reply.isPresent
  let C:=write r.replyPresent r.replyValue reply.value
  let D:=move r.replyValue r.replyOrigin
  obtain ⟨a,HA,ah,aw,aIO⟩:=write_exec source r.replyOrigin reply.isOrigin input c rowBase bound hi hc head hb
  have hia : a.inputHead ≤ input.length+1:=by rw [aIO.1];exact hi
  have hca : a.catalystHead ≤ a.catalyst.length:=by rw [aIO.2.1,aIO.2.2.1];exact hc
  obtain ⟨b,HB,bh,bw,bIO⟩:=write_exec r.replyOrigin r.replyPresent reply.isPresent input a rowBase bound hia hca ah hb
  have ioB:=sameIO_trans aIO bIO
  have hib : b.inputHead ≤ input.length+1:=by rw [ioB.1];exact hi
  have hcb : b.catalystHead ≤ b.catalyst.length:=by rw [ioB.2.1,ioB.2.2.1];exact hc
  obtain ⟨z,HZ,zh,zw,zIO⟩:=write_exec r.replyPresent r.replyValue reply.value input b rowBase bound hib hcb bh hb
  have ioZ:=sameIO_trans ioB zIO
  have hiz : z.inputHead ≤ input.length+1:=by rw [ioZ.1];exact hi
  have hcz : z.catalystHead ≤ z.catalyst.length:=by rw [ioZ.2.1,ioZ.2.2.1];exact hc
  obtain ⟨d,HD,dh,dw,dIO⟩:=move_exec r.replyValue r.replyOrigin input z rowBase bound hiz hcz zh hb
  have HA':=firstExit_mono input c _ _ _ _ _ _ F HA le_rfl (by simp [F]) (by simp)
  have HB':=firstExit_mono input a _ _ _ _ _ _ F HB le_rfl (by simp [F]) (by simp)
  have HZ':=firstExit_mono input b _ _ _ _ _ _ F HZ le_rfl (by simp [F]) (by simp)
  have HD':=firstExit_mono input z _ _ _ _ _ _ F HD le_rfl (by simp) (by simp)
  have HZD:=framed_seq C D input b z d _ _ bound F HZ' HD'
  let zd:=Sequential.rightConfig C D d
  have HBZD:=framed_seq B (Sequential.machine C D) input a b zd _ _ bound F HB' HZD
  let bzd:=Sequential.rightConfig B (Sequential.machine C D) zd
  have H:=framed_seq A (Sequential.machine B (Sequential.machine C D)) input c a bzd _ _ bound F HA' HBZD
  let out:=Sequential.rightConfig A (Sequential.machine B (Sequential.machine C D)) bzd
  refine ⟨out,H,dh,?_,sameIO_trans ioZ dIO⟩
  change d.work=_
  rw [dw,zw,bw,aw]

end CatalyticTreeEval.Contracts.NativeInputInspect
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeFramedBranch -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeRoundSupport

/-- Charge the real branch dispatch and retain the complete native child
frame, including the branch gate configuration itself. -/
theorem framed_branch_true {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (a : Config A) (time bound : ℕ) (F : Footprint)
    (flag : c.work c.workHead = true)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (H : FirstExit (A.step input)
      (fun _ e => e.workHead < bound ∧ Frame F c e) {e | e.state = none}
      (startOn A c) a time) :
    FirstExit ((Branch.machine A B).step input)
      (fun _ e => e.workHead < bound ∧ Frame F c e) {e | e.state = none}
      (startOn (Branch.machine A B) c) (Branch.leftConfig A B a) (1 + time) := by
  have H0 := branch_true A B input c a time flag hi hc (forget H)
  have V := visits_branch_true A B input c a time bound flag hi hc (forget H)
    (H.during 0 (by omega) _ rfl).1 (fun u hu e he => (H.during u hu e he).1)
  have Fr := frames_branch_true A B input c a time F flag hi hc (forget H)
    (fun u hu e he => (H.during u hu e he).2)
  exact { result := H0.result
          during := fun u hu e he => ⟨V u hu e he,Fr u hu e he⟩
          exit_mem := H0.exit_mem
          cut := H0.cut }

theorem framed_branch_false {N : Main.Machine} (A B : Main.Machine) (input : List Bool)
    (c : Config N) (b : Config B) (time bound : ℕ) (F : Footprint)
    (flag : c.work c.workHead = false)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (H : FirstExit (B.step input)
      (fun _ e => e.workHead < bound ∧ Frame F c e) {e | e.state = none}
      (startOn B c) b time) :
    FirstExit ((Branch.machine A B).step input)
      (fun _ e => e.workHead < bound ∧ Frame F c e) {e | e.state = none}
      (startOn (Branch.machine A B) c) (Branch.rightConfig A B b) (1 + time) := by
  have H0 := branch_false A B input c b time flag hi hc (forget H)
  have V := visits_branch_false A B input c b time bound flag hi hc (forget H)
    (H.during 0 (by omega) _ rfl).1 (fun u hu e he => (H.during u hu e he).1)
  have Fr := frames_branch_false A B input c b time F flag hi hc (forget H)
    (fun u hu e he => (H.during u hu e he).2)
  exact { result := H0.result
          during := fun u hu e he => ⟨V u hu e he,Fr u hu e he⟩
          exit_mem := H0.exit_mem
          cut := H0.cut }

end CatalyticTreeEval.Contracts.NativeRoundSupport
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeFramedBranchFamily -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeRoundSupport

def branchFamilyConfig (family : Bool → Main.Machine) :
    (bit : Bool) → Config (family bit) → Config (Branch.machine (family true) (family false))
  | true,c => Branch.leftConfig (family true) (family false) c
  | false,c => Branch.rightConfig (family true) (family false) c

@[simp] theorem branchFamily_workHead (family : Bool → Main.Machine) (bit : Bool) (c : Config (family bit)) :
    (branchFamilyConfig family bit c).workHead=c.workHead:=by cases bit <;> rfl

@[simp] theorem branchFamily_work (family : Bool → Main.Machine) (bit : Bool) (c : Config (family bit)) :
    (branchFamilyConfig family bit c).work=c.work:=by cases bit <;> rfl

@[simp] theorem branchFamily_inputHead (family : Bool → Main.Machine) (bit : Bool) (c : Config (family bit)) :
    (branchFamilyConfig family bit c).inputHead=c.inputHead:=by cases bit <;> rfl

@[simp] theorem branchFamily_catalystHead (family : Bool → Main.Machine) (bit : Bool) (c : Config (family bit)) :
    (branchFamilyConfig family bit c).catalystHead=c.catalystHead:=by cases bit <;> rfl

@[simp] theorem branchFamily_catalyst (family : Bool → Main.Machine) (bit : Bool) (c : Config (family bit)) :
    (branchFamilyConfig family bit c).catalyst=c.catalyst:=by cases bit <;> rfl

@[simp] theorem branchFamily_output (family : Bool → Main.Machine) (bit : Bool) (c : Config (family bit)) :
    (branchFamilyConfig family bit c).output=c.output:=by cases bit <;> rfl

/-- A uniform actual-Boolean branch rule. The finite parent table contains
both fixed child instances; the bit is read from its actual gate cell. -/
theorem framed_branch_family {N : Main.Machine} (family : Bool → Main.Machine) (bit : Bool)
    (input : List Bool) (c : Config N) (d : Config (family bit)) (time bound : ℕ) (F : Footprint)
    (flag : c.work c.workHead=bit)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (H : FirstExit ((family bit).step input)
      (fun _ e => e.workHead < bound ∧ Frame F c e) {e | e.state=none}
      (startOn (family bit) c) d time) :
    FirstExit ((Branch.machine (family true) (family false)).step input)
      (fun _ e => e.workHead < bound ∧ Frame F c e) {e | e.state=none}
      (startOn (Branch.machine (family true) (family false)) c)
      (branchFamilyConfig family bit d) (1+time) := by
  cases bit
  · exact framed_branch_false _ _ input c d time bound F flag hi hc H
  · exact framed_branch_true _ _ input c d time bound F flag hi hc H

end CatalyticTreeEval.Contracts.NativeRoundSupport
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeInputInspectPayload -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeInputInspect

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

theorem payloadReply_exec {N : Main.Machine} {lanes : ℕ} (r : Roles lanes) (value : Bool)
    (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+(lanes+1)+r.data.val)
    (hb : rowBase+(lanes+1)+lanes ≤ bound) :
    ∃ d : Config (payloadReply r value),
      FirstExit ((payloadReply r value).step input)
        (fun _ e => e.workHead < bound ∧ Frame (rowFootprint r rowBase) c e)
        {e | e.state=none} (startOn (payloadReply r value) c) d
        ((lanes+2)+replyTime r r.data) ∧ Post r rowBase (.bit value) c d := by
  let A:=NativeLiteral.machine .left (lanes+1) none
  let B:=writeReply r r.data (.bit value)
  let F:=rowFootprint r rowBase
  obtain ⟨a,HA,ah,aw,aIO⟩:=NativeLaneWordTransfer.move_exec .left (lanes+1) input c
    (rowBase+r.data.val) bound hi hc
    (by rw [NativeLiteral.position_left,head];omega) (by rw [head];omega) (by omega)
  have hia : a.inputHead ≤ input.length+1:=by rw [aIO.1];exact hi
  have hca : a.catalystHead ≤ a.catalyst.length:=by rw [aIO.2.1,aIO.2.2.1];exact hc
  obtain ⟨b,HB,bh,bw,bIO⟩:=writeReply_exec r r.data (.bit value) input a rowBase bound hia hca ah (by omega)
  have HA':=firstExit_mono input c _ _ _ _ _ _ F HA le_rfl (by simp) (by simp)
  have H:=framed_seq A B input c a b (lanes+2) (replyTime r r.data) bound F HA' HB
  let d:=Sequential.rightConfig A B b
  refine ⟨d,H,bh,?_,sameIO_trans aIO bIO⟩
  change b.work=replyWork r rowBase (.bit value) c.work
  rw [bw,aw]
  rfl

/-- Read a real payload bit one row after its tag, retain it through the
return hop in finite control, and write the corresponding local reply flags.
False and true payloads execute the two actual child tables of the branch. -/
theorem readPayload_exec {N : Main.Machine} {lanes : ℕ} (r : Roles lanes)
    (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+r.data.val) (hb : rowBase+(lanes+1)+lanes ≤ bound) :
    ∃ d : Config (readPayload r),
      FirstExit ((readPayload r).step input)
        (fun _ e => e.workHead < bound ∧ Frame (rowFootprint r rowBase) c e)
        {e | e.state=none} (startOn (readPayload r) c) d
        ((lanes+2)+(1+((lanes+2)+replyTime r r.data))) ∧
      Post r rowBase (.bit (c.work (rowBase+(lanes+1)+r.data.val))) c d := by
  let A:=NativeLiteral.machine .right (lanes+1) none
  let family:=payloadReply r
  let B:=Branch.machine (family true) (family false)
  let F:=rowFootprint r rowBase
  let bit:=c.work (rowBase+(lanes+1)+r.data.val)
  obtain ⟨a,HA,ah,aw,aIO⟩:=NativeLaneWordTransfer.move_exec .right (lanes+1) input c
    (rowBase+(lanes+1)+r.data.val) bound hi hc
    (by rw [NativeLiteral.position_right,head];omega) (by rw [head];omega) (by omega)
  have hia : a.inputHead ≤ input.length+1:=by rw [aIO.1];exact hi
  have hca : a.catalystHead ≤ a.catalyst.length:=by rw [aIO.2.1,aIO.2.2.1];exact hc
  obtain ⟨b,HB,bPost⟩:=payloadReply_exec r bit input a rowBase bound hia hca ah hb
  have gate : a.work a.workHead=bit:=by rw [aw,ah]
  have HBranch:=framed_branch_family family bit input a b _ bound F gate hia hca HB
  let branchEnd:=branchFamilyConfig family bit b
  have HA':=firstExit_mono input c _ _ _ _ _ _ F HA le_rfl (by simp) (by simp)
  have H:=framed_seq A B input c a branchEnd (lanes+2) (1+((lanes+2)+replyTime r r.data)) bound F HA' HBranch
  let d:=Sequential.rightConfig A B branchEnd
  refine ⟨d,H,?_,?_,?_⟩
  · change branchEnd.workHead=_
    rw [branchFamily_workHead]
    exact bPost.1
  · change branchEnd.work=replyWork r rowBase (.bit bit) c.work
    rw [branchFamily_work,bPost.2.1,aw]
  · change SameIO c branchEnd
    simpa only [branchEnd,SameIO,branchFamily_inputHead,branchFamily_catalystHead,branchFamily_catalyst,
      branchFamily_output] using sameIO_trans aIO bPost.2.2

end CatalyticTreeEval.Contracts.NativeInputInspect
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeInputInspect -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeInputInspect

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

theorem dataCase_exec {N : Main.Machine} {lanes : ℕ} (r : Roles lanes) (tag : Bool)
    (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+r.data.val) (hb : rowBase+(lanes+1)+lanes ≤ bound) :
    ∃ d : Config (dataCase r tag),
      FirstExit ((dataCase r tag).step input)
        (fun _ e => e.workHead < bound ∧ Frame (rowFootprint r rowBase) c e)
        {e | e.state=none} (startOn (dataCase r tag) c) d (dataTime r tag) ∧
      Post r rowBase (dataReply r rowBase tag c.work) c d := by
  cases tag
  · obtain ⟨d,H,dh,dw,dIO⟩:=writeReply_exec r r.data .eof input c rowBase bound hi hc head (by omega)
    exact ⟨d,H,dh,dw,dIO⟩
  · exact readPayload_exec r input c rowBase bound hi hc head hb

theorem readData_exec {N : Main.Machine} {lanes : ℕ} (r : Roles lanes)
    (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+r.data.val) (hb : rowBase+(lanes+1)+lanes ≤ bound) :
    ∃ d : Config (readData r),
      FirstExit ((readData r).step input)
        (fun _ e => e.workHead < bound ∧ Frame (rowFootprint r rowBase) c e)
        {e | e.state=none} (startOn (readData r) c) d
        (1+dataTime r (c.work (rowBase+r.data.val))) ∧
      Post r rowBase (dataReply r rowBase (c.work (rowBase+r.data.val)) c.work) c d := by
  let tag:=c.work (rowBase+r.data.val)
  let family:=dataCase r
  obtain ⟨a,H,post⟩:=dataCase_exec r tag input c rowBase bound hi hc head hb
  have HG:=framed_branch_family family tag input c a _ bound (rowFootprint r rowBase)
    (by rw [head]) hi hc H
  refine ⟨branchFamilyConfig family tag a,HG,?_,?_,?_⟩
  · rw [branchFamily_workHead];exact post.1
  · rw [branchFamily_work];exact post.2.1
  · simpa only [SameIO,branchFamily_inputHead,branchFamily_catalystHead,branchFamily_catalyst,
      branchFamily_output] using post.2.2

theorem nonOrigin_exec {N : Main.Machine} {lanes : ℕ} (r : Roles lanes)
    (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+r.origin.val) (hb : rowBase+(lanes+1)+lanes ≤ bound) :
    ∃ d : Config (nonOrigin r),
      FirstExit ((nonOrigin r).step input)
        (fun _ e => e.workHead < bound ∧ Frame (rowFootprint r rowBase) c e)
        {e | e.state=none} (startOn (nonOrigin r) c) d
        ((NativeLaneFlagCopy.distance r.origin r.data+1)+
          (1+dataTime r (c.work (rowBase+r.data.val)))) ∧
      Post r rowBase (dataReply r rowBase (c.work (rowBase+r.data.val)) c.work) c d := by
  let A:=move r.origin r.data
  let B:=readData r
  let F:=rowFootprint r rowBase
  obtain ⟨a,HA,ah,aw,aIO⟩:=move_exec r.origin r.data input c rowBase bound hi hc head (by omega)
  have hia : a.inputHead ≤ input.length+1:=by rw [aIO.1];exact hi
  have hca : a.catalystHead ≤ a.catalyst.length:=by rw [aIO.2.1,aIO.2.2.1];exact hc
  obtain ⟨b,HB,post⟩:=readData_exec r input a rowBase bound hia hca ah hb
  rw [aw] at HB post
  have HA':=firstExit_mono input c _ _ _ _ _ _ F HA le_rfl (by simp) (by simp)
  have H:=framed_seq A B input c a b _ _ bound F HA' HB
  let d:=Sequential.rightConfig A B b
  refine ⟨d,H,post.1,?_,sameIO_trans aIO post.2.2⟩
  change b.work=replyWork r rowBase _ c.work
  rw [post.2.1,aw]

theorem originCase_exec {N : Main.Machine} {lanes : ℕ} (r : Roles lanes) (atOrigin : Bool)
    (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+r.origin.val) (hb : rowBase+(lanes+1)+lanes ≤ bound) :
    ∃ d : Config (originCase r atOrigin),
      FirstExit ((originCase r atOrigin).step input)
        (fun _ e => e.workHead < bound ∧ Frame (rowFootprint r rowBase) c e)
        {e | e.state=none} (startOn (originCase r atOrigin) c) d
        (originTime r rowBase c.work atOrigin) ∧
      Post r rowBase (if atOrigin then .origin else dataReply r rowBase (c.work (rowBase+r.data.val)) c.work) c d := by
  cases atOrigin
  · exact nonOrigin_exec r input c rowBase bound hi hc head hb
  · obtain ⟨d,H,dh,dw,dIO⟩:=writeReply_exec r r.origin .origin input c rowBase bound hi hc head (by omega)
    exact ⟨d,H,dh,dw,dIO⟩

/-- The complete actual buffered-input inspection circuit. It distinguishes
origin, EOF and either payload bit through native branches, returns at the
first reply flag, preserves every other work cell and keeps IO stationary. -/
theorem machine_exec {N : Main.Machine} {lanes : ℕ} (r : Roles lanes)
    (input : List Bool) (c : Config N) (rowBase bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=rowBase+r.bookmark.val) (hb : rowBase+(lanes+1)+lanes ≤ bound) :
    ∃ d : Config (machine r),
      FirstExit ((machine r).step input)
        (fun _ e => e.workHead < bound ∧ Frame (rowFootprint r rowBase) c e)
        {e | e.state=none} (startOn (machine r) c) d
        ((NativeLaneFlagCopy.distance r.bookmark r.origin+1)+
          (1+originTime r rowBase c.work (c.work (rowBase+r.origin.val)))) ∧
      Post r rowBase (localReply r rowBase c.work) c d := by
  let A:=move r.bookmark r.origin
  let family:=originCase r
  let B:=Branch.machine (family true) (family false)
  let F:=rowFootprint r rowBase
  let atOrigin:=c.work (rowBase+r.origin.val)
  obtain ⟨a,HA,ah,aw,aIO⟩:=move_exec r.bookmark r.origin input c rowBase bound hi hc head (by omega)
  have hia : a.inputHead ≤ input.length+1:=by rw [aIO.1];exact hi
  have hca : a.catalystHead ≤ a.catalyst.length:=by rw [aIO.2.1,aIO.2.2.1];exact hc
  obtain ⟨b,HB,post⟩:=originCase_exec r atOrigin input a rowBase bound hia hca ah hb
  rw [aw] at HB post
  have gate : a.work a.workHead=atOrigin:=by rw [aw,ah]
  have HBranch:=framed_branch_family family atOrigin input a b _ bound F gate hia hca HB
  let branchEnd:=branchFamilyConfig family atOrigin b
  have HA':=firstExit_mono input c _ _ _ _ _ _ F HA le_rfl (by simp) (by simp)
  have H:=framed_seq A B input c a branchEnd _ _ bound F HA' HBranch
  let d:=Sequential.rightConfig A B branchEnd
  refine ⟨d,H,?_,?_,?_⟩
  · change branchEnd.workHead=_
    rw [branchFamily_workHead];exact post.1
  · change branchEnd.work=replyWork r rowBase (localReply r rowBase c.work) c.work
    rw [branchFamily_work,post.2.1,aw]
    rfl
  · change SameIO c branchEnd
    simpa only [branchEnd,SameIO,branchFamily_inputHead,branchFamily_catalystHead,branchFamily_catalyst,
      branchFamily_output] using sameIO_trans aIO post.2.2

end CatalyticTreeEval.Contracts.NativeInputInspect
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeCatalystStationary -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeHeadStationary

open CatalyticMatching.General
open NativeRoundSupport

theorem step_position (head : Head) (M : Main.Machine) (H : Stationary head M)
    (input : List Bool) {c d : Config M} (step : M.step input c=some d) :
    position head d=position head c := by
  cases hs : c.state with
  | none =>
      have eq : c=d := by simpa [Machine.step,hs] using step
      cases eq
      rfl
  | some q =>
      unfold Machine.step at step
      rw [hs] at step
      let a := M.table q (if c.inputHead=0 then none else input[c.inputHead-1]?)
        (c.work c.workHead) c.catalyst[c.catalystHead]?
        (c.inputHead==0) (c.workHead==0) (c.catalystHead==0)
      change (if a.inputMove.apply c.inputHead ≤ input.length+1 ∧
          a.catalystMove.apply c.catalystHead ≤ c.catalyst.length ∧
          (a.catalystWrite.isSome → c.catalystHead < c.catalyst.length) then
        some (Configuration.mk a.next (a.inputMove.apply c.inputHead) (a.workMove.apply c.workHead)
          (a.catalystMove.apply c.catalystHead) (Function.update c.work c.workHead a.workWrite)
          (match a.catalystWrite with | none => c.catalyst | some b => c.catalyst.set c.catalystHead b)
          (c.output ++ a.emit.toList)) else none)=some d at step
      split at step
      · cases Option.some.inj step
        have HM : motion head a=.stay := H q (if c.inputHead=0 then none else input[c.inputHead-1]?)
          (c.work c.workHead) c.catalyst[c.catalystHead]?
          (c.inputHead==0) (c.workHead==0) (c.catalystHead==0)
        cases head
        · simpa [position,motion,Move.apply] using congrArg (fun move => move.apply c.inputHead) HM
        · simpa [position,motion,Move.apply] using congrArg (fun move => move.apply c.catalystHead) HM
      · contradiction

/-- Every successful prefix retains the physical head, including the endpoint. -/
theorem run_position (head : Head) (M : Main.Machine) (H : Stationary head M)
    (input : List Bool) (c : Config M) {time : ℕ} {d : Config M}
    (run : runFrom (M.step input) c time=some d) : position head d=position head c := by
  induction time generalizing d with
  | zero =>
      have eq : c=d := by simpa only [runFrom_zero,Option.some.injEq] using run
      cases eq
      rfl
  | succ n ih =>
      cases hr : runFrom (M.step input) c n with
      | none => simp [runFrom_succ,hr] at run
      | some e =>
          have hs : M.step input e=some d := by simpa [runFrom_succ,hr] using run
          exact (step_position head M H input hs).trans (ih hr)

theorem sequential (head : Head) (A B : Main.Machine)
    (HA : Stationary head A) (HB : Stationary head B) :
    Stationary head (Sequential.machine A B) := by
  intro q input work catalyst io wo co
  cases hq : finSumFinEquiv.symm q with
  | inl qa =>
      cases head <;> simpa [motion,Sequential.machine,hq,Sequential.leftInstruction] using
        HA qa input work catalyst io wo co
  | inr qb =>
      cases head <;> simpa [motion,Sequential.machine,hq,Sequential.rightInstruction] using
        HB qb input work catalyst io wo co

theorem branch (head : Head) (A B : Main.Machine)
    (HA : Stationary head A) (HB : Stationary head B) :
    Stationary head (Branch.machine A B) := by
  intro q input work catalyst io wo co
  cases hq : finSumFinEquiv.symm q with
  | inl gate =>
      cases head <;> simp [motion,Branch.machine,hq,Branch.gateInstruction]
  | inr r =>
      cases hr : finSumFinEquiv.symm r with
      | inl qa =>
          cases head <;> simpa [motion,Branch.machine,hq,hr,Branch.leftInstruction] using
            HA qa input work catalyst io wo co
      | inr qb =>
          cases head <;> simpa [motion,Branch.machine,hq,hr,Branch.rightInstruction] using
            HB qb input work catalyst io wo co

theorem reentry (head : Head) (A : Main.Machine) (entry : Fin A.states)
    (HA : Stationary head A) : Stationary head (Reentry.machine A entry) := HA

theorem whileFlag (head : Head) (A : Main.Machine) (HA : Stationary head A) :
    Stationary head (WhileFlag.machine A) := by
  intro q input work catalyst io wo co
  cases hq : finSumFinEquiv.symm q with
  | inl gate =>
      cases head <;> simp [motion,WhileFlag.machine,hq,WhileFlag.gateInstruction]
  | inr qa =>
      cases head <;> simpa [motion,WhileFlag.machine,hq,WhileFlag.bodyInstruction] using
        HA qa input work catalyst io wo co

theorem taggedReturn (head : Head) (A : Main.Machine) (tags : ℕ) (HA : Stationary head A) :
    Stationary head (TaggedReturn.machine A tags) := by
  intro q input work catalyst io wo co
  cases hs : ((TaggedReturn.encode A tags).symm q).2 with
  | none =>
      cases head <;> simp [motion,TaggedReturn.machine,hs]
  | some qa =>
      cases head <;> simpa [motion,TaggedReturn.machine,hs,TaggedReturn.liftInstruction] using
        HA qa input work catalyst io wo co

theorem workLane_instruction (head : Head) (A : Main.Machine) (lanes : ℕ) (lane : Fin lanes)
    (HA : Stationary head A) (q : WorkLanes.Control A lanes)
    (input : Option Bool) (work : Bool) (catalyst : Option Bool) (io co : Bool) :
    motion head (WorkLanes.instruction A lanes lane q input work catalyst io co)=.stay := by
  rcases q with p | p
  · rcases p with ⟨qa,r⟩
    by_cases hz : r.val=0 <;>
      cases head <;> simp [motion,WorkLanes.instruction,hz,WorkLanes.quietInstruction]
  · rcases p with p | p
    · rcases p with ⟨qa,origin,r⟩
      by_cases hz : r.val=0
      · cases head <;> simpa [motion,WorkLanes.instruction,hz,WorkLanes.applyInstruction] using
          HA qa input work catalyst io origin co
      · cases head <;> simp [motion,WorkLanes.instruction,hz,WorkLanes.quietInstruction]
    · rcases p with ⟨next,direction,r⟩
      cases head <;> simp [motion,WorkLanes.instruction,WorkLanes.quietInstruction]

theorem workLanes (head : Head) (A : Main.Machine) (lanes : ℕ) (lane : Fin lanes)
    (HA : Stationary head A) : Stationary head (WorkLanes.machine A lanes lane) := by
  intro q input work catalyst io wo co
  exact workLane_instruction head A lanes lane HA ((WorkLanes.encode A lanes).symm q)
    input work catalyst io co

/-- Replace a catalyst-length envelope by the exact stationary head interval.
This is valid uniformly for every longer catalyst suffix. -/
theorem firstExit_envelope {M : Main.Machine} (input : List Bool) (c d : Config M)
    (time bound : ℕ) (F : Footprint) (stationary : CatalystStationary M)
    (H : FirstExit (M.step input) (fun _ e => e.workHead < bound ∧ Frame F c e)
      {e | e.state=none} c d time) :
    FirstExit (M.step input)
      (fun _ e => (Envelope.mk 0 bound c.catalystHead (c.catalystHead+1)).Contains e ∧ Frame F c e)
      {e | e.state=none} c d time := by
  refine { result := H.result, exit_mem := H.exit_mem, cut := H.cut, during := ?_ }
  intro u hu e he
  have HE := H.during u hu e he
  have HP := run_position .catalyst M stationary input c he
  change e.catalystHead=c.catalystHead at HP
  change (0 ≤ e.workHead ∧ e.workHead < bound ∧ c.catalystHead ≤ e.catalystHead ∧
    e.catalystHead < c.catalystHead+1) ∧ Frame F c e
  exact ⟨⟨Nat.zero_le _,HE.1,by omega,by omega⟩,HE.2⟩

end CatalyticTreeEval.Contracts.NativeHeadStationary
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeArithmeticStationary -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeHeadStationary

open CatalyticMatching.General

theorem literal (head : Head) (direction : Move) (moves : ℕ) (bit : Option Bool) :
    Stationary head (NativeLiteral.machine direction moves bit) := by
  intro q input work catalyst io wo co
  by_cases h : q.val < moves <;>
    cases head <;> simp [motion,NativeLiteral.machine,h]

theorem rippleAdder (head : Head) : Stationary head RippleAdder.machine := by
  intro q input work catalyst io wo co
  fin_cases q <;> cases head <;> rfl

theorem rippleSubtractor (head : Head) : Stationary head RippleSubtractor.machine := by
  intro q input work catalyst io wo co
  fin_cases q <;> cases head <;> rfl

theorem shiftAppend (head : Head) : Stationary head ShiftAppend.machine := by
  intro q input work catalyst io wo co
  fin_cases q <;> cases head <;> rfl

theorem taggedRewind (head : Head) (toBank : Bool) : Stationary head (TaggedRewind.machine toBank) := by
  intro q input work catalyst io wo co
  fin_cases q <;> cases head <;> cases work <;> rfl

theorem countdown (head : Head) : Stationary head (BinaryCountdown.machine false) := by
  intro q input work catalyst io wo co
  fin_cases q <;> cases head <;> rfl

theorem saveCarry (head : Head) (bit : Bool) : Stationary head (ConsumeMSB.saveCarry bit) :=
  sequential head _ _ (literal head .stay 0 (some false))
    (sequential head _ _ (taggedRewind head false) (literal head .stay 0 (some bit)))

theorem consumeMSB (head : Head) : Stationary head ConsumeMSB.machine :=
  sequential head _ _ (literal head .right 6 none)
    (sequential head _ _ (shiftAppend head)
      (branch head _ _ (saveCarry head true) (saveCarry head false)))

theorem clearCarry (head : Head) : Stationary head RestoringRound.clearCarry :=
  literal head .stay 0 (some false)

theorem restore (head : Head) : Stationary head RestoringRound.restore :=
  sequential head _ _ (taggedRewind head true)
    (sequential head _ _ (rippleAdder head) (clearCarry head))

theorem bankAdd (head : Head) : Stationary head NativeBankAdd.machine :=
  sequential head _ _ (literal head .right 6 none)
    (sequential head _ _ (rippleAdder head)
      (sequential head _ _ (clearCarry head) (taggedRewind head false)))

theorem modTrial (head : Head) : Stationary head NativeQuotientRound.trial :=
  sequential head _ _ (rippleSubtractor head)
    (branch head _ _ (saveCarry head true)
      (sequential head _ _ (restore head) (saveCarry head false)))

theorem modReduce (head : Head) : Stationary head NativeModReduce.machine :=
  sequential head _ _ (literal head .right 6 none) (modTrial head)

theorem multiplyRound (head : Head) : Stationary head NativeMultiplyRound.machine :=
  branch head _ _ (sequential head _ _ (consumeMSB head) (bankAdd head)) (consumeMSB head)

theorem restoringTrial (head : Head) : Stationary head RestoringRound.trial :=
  sequential head _ _ (rippleSubtractor head)
    (branch head _ _ (clearCarry head) (restore head))

theorem restoringBankRound (head : Head) (incoming : Bool) :
    Stationary head (RestoringRound.bankRound incoming) :=
  sequential head _ _ (reentry head _ _ (shiftAppend head))
    (sequential head _ _ (taggedRewind head true) (restoringTrial head))

theorem restoringFlagRound (head : Head) (incoming : Bool) :
    Stationary head (RestoringRound.flagRound incoming) :=
  sequential head _ _ (restoringBankRound head incoming) (taggedRewind head false)

theorem restoringRound (head : Head) : Stationary head RestoringRound.machine :=
  branch head _ _
    (sequential head _ _ (literal head .right 6 none) (restoringFlagRound head true))
    (sequential head _ _ (literal head .right 6 none) (restoringFlagRound head false))

theorem laneFlagCopy {lanes : ℕ} (head : Head) (source target : Fin lanes) :
    Stationary head (NativeLaneFlagCopy.machine source target) := by
  have arm (bit : Bool) : Stationary head (NativeLaneFlagCopy.arm source target bit) :=
    sequential head _ _ (literal head _ _ (some bit)) (literal head _ _ none)
  exact branch head _ _ (arm true) (arm false)

theorem moveFlag {lanes : ℕ} (head : Head) (source target : Fin lanes) :
    Stationary head (NativeMSBFold.moveFlag source target) := literal head _ _ none

theorem msbFeed {lanes : ℕ} (head : Head) (counter source arithmetic : Fin lanes) :
    Stationary head (NativeMSBFold.feed counter source arithmetic) :=
  sequential head _ _ (moveFlag head counter source)
    (sequential head _ _ (workLanes head _ _ _ (consumeMSB head))
      (sequential head _ _ (laneFlagCopy head source arithmetic) (moveFlag head source arithmetic)))

theorem msbBodyWith {lanes : ℕ} (head : Head) (counter source arithmetic : Fin lanes)
    (round : Main.Machine) (Hround : Stationary head round) :
    Stationary head (NativeMSBFold.bodyWith counter source arithmetic round) :=
  sequential head _ _ (msbFeed head counter source arithmetic)
    (sequential head _ _ Hround
      (sequential head _ _ (moveFlag head arithmetic counter) (workLanes head _ _ _ (countdown head))))

theorem msbFoldWith {lanes : ℕ} (head : Head) (counter source arithmetic : Fin lanes)
    (round : Main.Machine) (Hround : Stationary head round) :
    Stationary head (NativeMSBFold.machineWith counter source arithmetic round) :=
  whileFlag head _ (msbBodyWith head counter source arithmetic round Hround)

theorem msbFold {lanes : ℕ} (head : Head) (counter source arithmetic : Fin lanes)
    (round : Main.Machine) (Hround : Stationary head round) :
    Stationary head (NativeMSBFold.machine counter source arithmetic round) :=
  msbFoldWith head counter source arithmetic _ (workLanes head _ _ _ Hround)

theorem wordTransfer {lanes : ℕ} (head : Head) (source target : Fin lanes) (targetB consume : Bool) :
    Stationary head (NativeLaneWordTransfer.machine source target targetB consume) := by
  have arm (bit : Bool) : Stationary head (NativeLaneWordTransfer.bitArm source target targetB consume bit) :=
    sequential head _ _ (literal head _ _ (some bit)) (literal head _ _ _)
  have hop : Stationary head (NativeLaneWordTransfer.bitHop source target targetB consume) :=
    branch head _ _ (arm true) (arm false)
  have body : Stationary head (NativeLaneWordTransfer.forwardBody source target targetB consume) :=
    sequential head _ _ (literal head _ _ none) (sequential head _ _ hop (literal head _ _ none))
  have back : Stationary head (NativeLaneWordTransfer.backStep lanes) := literal head _ _ none
  have rewind : Stationary head (NativeLaneWordTransfer.rewind lanes) :=
    sequential head _ _ back (sequential head _ _ (whileFlag head _ back) back)
  exact sequential head _ _ (literal head _ _ none)
    (sequential head _ _ (whileFlag head _ body) rewind)

end CatalyticTreeEval.Contracts.NativeHeadStationary
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeStationaryPort -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeHeadStationary

open NativeRoundSupport

/-- Heterogeneous entry variant of the stationary envelope law. Keeping the
original caller as the frame baseline avoids comparing unrelated finite-control
types merely to erase their state fields. -/
theorem firstExit_port_envelope {N M : Main.Machine} (input : List Bool)
    (c : Config N) (d : Config M) (time bound : ℕ) (F : Footprint)
    (stationary : CatalystStationary M)
    (H : FirstExit (M.step input) (fun _ e => e.workHead < bound ∧ Frame F c e)
      {e | e.state=none} (startOn M c) d time) :
    FirstExit (M.step input)
      (fun _ e => (Envelope.mk 0 bound c.catalystHead (c.catalystHead+1)).Contains e ∧ Frame F c e)
      {e | e.state=none} (startOn M c) d time := by
  refine { result := H.result, exit_mem := H.exit_mem, cut := H.cut, during := ?_ }
  intro u hu e he
  have HE := H.during u hu e he
  have HP := run_position .catalyst M stationary input (startOn M c) he
  change e.catalystHead=c.catalystHead at HP
  change (0 ≤ e.workHead ∧ e.workHead < bound ∧ c.catalystHead ≤ e.catalystHead ∧
    e.catalystHead < c.catalystHead+1) ∧ Frame F c e
  exact ⟨⟨Nat.zero_le _,HE.1,by omega,by omega⟩,HE.2⟩

end CatalyticTreeEval.Contracts.NativeHeadStationary
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeInputInspectResource -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeInputInspect

open NativeRoundSupport NativeHeadStationary

theorem distance_le {lanes : ℕ} (source target : Fin lanes) :
    NativeLaneFlagCopy.distance source target ≤ lanes := by
  unfold NativeLaneFlagCopy.distance
  split_ifs <;> omega

theorem replyTime_le {lanes : ℕ} (r : Roles lanes) (source : Fin lanes) :
    replyTime r source ≤ 4*lanes+4 := by
  have h1:=distance_le source r.replyOrigin
  have h2:=distance_le r.replyOrigin r.replyPresent
  have h3:=distance_le r.replyPresent r.replyValue
  have h4:=distance_le r.replyValue r.replyOrigin
  unfold replyTime
  omega

theorem dataTime_le {lanes : ℕ} (r : Roles lanes) (tag : Bool) :
    dataTime r tag ≤ 6*lanes+9 := by
  have h:=replyTime_le r r.data
  cases tag <;> simp only [dataTime,Bool.false_eq_true,if_false,if_true] <;> omega

theorem originTime_le {lanes : ℕ} (r : Roles lanes) (rowBase : ℕ)
    (work : ℕ → Bool) (origin : Bool) :
    originTime r rowBase work origin ≤ 7*lanes+11 := by
  have h1:=replyTime_le r r.origin
  have h2:=distance_le r.origin r.data
  have h3:=dataTime_le r (work (rowBase+r.data.val))
  cases origin <;> simp only [originTime,Bool.false_eq_true,if_false,if_true] <;> omega

/-- Inspection has constant finite-lane overhead; input length and cursor
position enter neither this bound nor the transition table. -/
theorem time_le {lanes : ℕ} (r : Roles lanes) (rowBase : ℕ) (work : ℕ → Bool) :
    (NativeLaneFlagCopy.distance r.bookmark r.origin+1)+
      (1+originTime r rowBase work (work (rowBase+r.origin.val))) ≤ 8*lanes+13 := by
  have h1:=distance_le r.bookmark r.origin
  have h2:=originTime_le r rowBase work (work (rowBase+r.origin.val))
  omega

theorem move_stationary {lanes : ℕ} (head : Head) (source target : Fin lanes) :
    Stationary head (move source target) := literal head _ _ _

theorem write_stationary {lanes : ℕ} (head : Head) (source target : Fin lanes) (value : Bool) :
    Stationary head (write source target value) := literal head _ _ _

theorem reply_stationary {lanes : ℕ} (head : Head) (r : Roles lanes) (source : Fin lanes) (reply : Reply) :
    Stationary head (writeReply r source reply) :=
  sequential head _ _ (write_stationary head _ _ _)
    (sequential head _ _ (write_stationary head _ _ _)
      (sequential head _ _ (write_stationary head _ _ _) (move_stationary head _ _)))

theorem payload_stationary {lanes : ℕ} (head : Head) (r : Roles lanes) (value : Bool) :
    Stationary head (payloadReply r value) :=
  sequential head _ _ (literal head _ _ _) (reply_stationary head r r.data (.bit value))

theorem readPayload_stationary {lanes : ℕ} (head : Head) (r : Roles lanes) :
    Stationary head (readPayload r) :=
  sequential head _ _ (literal head _ _ _)
    (branch head _ _ (payload_stationary head r true) (payload_stationary head r false))

theorem readData_stationary {lanes : ℕ} (head : Head) (r : Roles lanes) :
    Stationary head (readData r) :=
  branch head _ _ (readPayload_stationary head r) (reply_stationary head r r.data .eof)

theorem nonOrigin_stationary {lanes : ℕ} (head : Head) (r : Roles lanes) :
    Stationary head (nonOrigin r) :=
  sequential head _ _ (move_stationary head r.origin r.data) (readData_stationary head r)

theorem stationary {lanes : ℕ} (head : Head) (r : Roles lanes) :
    Stationary head (machine r) :=
  sequential head _ _ (move_stationary head r.bookmark r.origin)
    (branch head _ _ (reply_stationary head r r.origin .origin) (nonOrigin_stationary head r))

theorem firstExit_envelope {N : Main.Machine} {lanes : ℕ} (r : Roles lanes)
    (input : List Bool) (c : Config N) (d : Config (machine r)) (rowBase bound T : ℕ)
    (H : FirstExit ((machine r).step input)
      (fun _ e => e.workHead < bound ∧ Frame (rowFootprint r rowBase) c e)
      {e | e.state=none} (startOn (machine r) c) d T) :
    FirstExit ((machine r).step input)
      (fun _ e => (Envelope.mk 0 bound c.catalystHead (c.catalystHead+1)).Contains e ∧
        Frame (rowFootprint r rowBase) c e)
      {e | e.state=none} (startOn (machine r) c) d T :=
  firstExit_port_envelope input c d T bound _ (stationary .catalyst r) H

end CatalyticTreeEval.Contracts.NativeInputInspect
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeInputProbe -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeInputProbe

open NativeRoundSupport
open NativeInputInspect (Roles Post rowFootprint localReply)
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

/-- Complete finite probe on the actual physical tape. InputHead is a proof
index identifying the sole true bookmark, not an argument to machine code.
Every crossed marker cell and every branch/hop is included in the time. -/
theorem machine_exec {N : Main.Machine} {lanes : ℕ} (r : Roles lanes)
    (input : List Bool) (c : Config N) (base inputHead : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=base+lanes)
    (cursor : ∀ j ≤ inputHead,
      c.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead)) :
    ∃ d : Config (machine r),
      FirstExit ((machine r).step input)
        (fun _ e => e.workHead < bound lanes base inputHead ∧
          Frame (rowFootprint r (rowBase lanes base inputHead)) c e)
        {e | e.state=none} (startOn (machine r) c) d (time r base inputHead c.work) ∧
      Post r (rowBase lanes base inputHead)
        (localReply r (rowBase lanes base inputHead) c.work) c d := by
  let A:=NativeInputLocate.machine r.bookmark
  let B:=NativeInputInspect.machine r
  let rb:=rowBase lanes base inputHead
  let ub:=bound lanes base inputHead
  let F:=rowFootprint r rb
  have capacity : rb+(lanes+1)+lanes ≤ ub:=by
    dsimp [rb,ub,rowBase,bound]
    nlinarith
  have tagBound : WorkLanes.address r.bookmark base (3+3*inputHead) < ub:=by
    dsimp [WorkLanes.address,ub,bound]
    nlinarith [r.bookmark.isLt]
  obtain ⟨a,HA,ah,aw,aIO⟩:=NativeInputLocate.machine_exec r.bookmark input c base inputHead ub hi hc head cursor tagBound
  have hia : a.inputHead ≤ input.length+1:=by rw [aIO.1];exact hi
  have hca : a.catalystHead ≤ a.catalyst.length:=by rw [aIO.2.1,aIO.2.2.1];exact hc
  have hhead : a.workHead=rb+r.bookmark.val:=ah
  obtain ⟨b,HB,post⟩:=NativeInputInspect.machine_exec r input a rb ub hia hca hhead capacity
  rw [aw] at HB post
  have HA':=firstExit_mono input c _ _ _ _ _ _ F HA le_rfl (by simp) (by simp)
  have H:=framed_seq A B input c a b _ _ ub F HA' HB
  let d:=Sequential.rightConfig A B b
  refine ⟨d,H,post.1,?_,sameIO_trans aIO post.2.2⟩
  change b.work=NativeInputInspect.replyWork r rb _ c.work
  rw [post.2.1,aw]

theorem time_le {lanes : ℕ} (r : Roles lanes) (base inputHead : ℕ) (work : ℕ → Bool) :
    time r base inputHead work ≤ 20*(lanes+1)*(inputHead+1) := by
  have h1:=NativeInputInspect.time_le r (rowBase lanes base inputHead) work
  have hd : NativeInputLocate.entryDistance r.bookmark ≤ 3*(lanes+1):=by
    unfold NativeInputLocate.entryDistance
    omega
  rw [time,NativeInputLocate.time,NativeInputLocate.padding_succ]
  nlinarith

end CatalyticTreeEval.Contracts.NativeInputProbe
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeInputProbeBuffer -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeInputProbe

open NativeInputInspect (Roles Reply Post localReply dataReply)
open NativeRoundSupport

/-- The finite probe's observed cells equal the source input semantics,
including distinct origin/EOF and false/true data cases. -/
theorem localReply_eq {lanes : ℕ} (r : Roles lanes) (base inputHead : ℕ)
    (params : List Bool) (work : ℕ → Bool)
    (buffer : Buffer r base params work) (headBound : inputHead ≤ params.length+1) :
    localReply r (rowBase lanes base inputHead) work=readReply params inputHead := by
  have ho : work (rowBase lanes base inputHead+r.origin.val)=decide (inputHead=0):=by
    change work (WorkLanes.address r.origin base (3+3*inputHead))=_
    rw [buffer.origin]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  by_cases hz : inputHead=0
  · subst inputHead
    simp [localReply,ho,readReply]
  have hoff : work (rowBase lanes base inputHead+r.origin.val)=false:=by simpa only [hz,decide_false] using ho
  by_cases hin : inputHead ≤ params.length
  · have hi : inputHead-1 < params.length:=by omega
    have ht : work (rowBase lanes base inputHead+r.data.val)=true:=by
      change work (WorkLanes.address r.data base (3+3*inputHead))=true
      rw [show 3+3*inputHead=6+3*(inputHead-1) by omega]
      exact buffer.tags _ hi
    have hv : work (rowBase lanes base inputHead+(lanes+1)+r.data.val)=params[inputHead-1]:=by
      have pos : rowBase lanes base inputHead+(lanes+1)+r.data.val=
          WorkLanes.address r.data base (7+3*(inputHead-1)):=by
        have he : 7+3*(inputHead-1)=(3+3*inputHead)+1:=by omega
        rw [he]
        dsimp [rowBase,WorkLanes.address]
        ring
      rw [pos]
      exact buffer.values _ hi
    simp only [localReply,hoff,Bool.false_eq_true,if_false,dataReply,ht,if_true,
      readReply,hz,List.getElem?_eq_getElem hi,hv]
  · have he : inputHead=params.length+1:=by omega
    have ht : work (rowBase lanes base inputHead+r.data.val)=false:=by
      change work (WorkLanes.address r.data base (3+3*inputHead))=false
      rw [show 3+3*inputHead=6+3*params.length by omega]
      exact buffer.terminator
    simp only [localReply,hoff,Bool.false_eq_true,if_false,dataReply,ht,readReply,hz]
    rw [show inputHead-1=params.length by omega]
    simp

/-- Native virtual-input observation from a physical buffered-input invariant.
The sole cursor is located by actual marker search; no input oracle is assumed. -/
theorem reads_input {N : Main.Machine} {lanes : ℕ} (r : Roles lanes)
    (input params : List Bool) (c : Config N) (base inputHead : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=base+lanes)
    (cursor : ∀ j ≤ inputHead,
      c.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead))
    (buffer : Buffer r base params c.work) (headBound : inputHead ≤ params.length+1) :
    ∃ d : Config (machine r),
      FirstExit ((machine r).step input)
        (fun _ e => e.workHead < bound lanes base inputHead ∧
          Frame (NativeInputInspect.rowFootprint r (rowBase lanes base inputHead)) c e)
        {e | e.state=none} (startOn (machine r) c) d (time r base inputHead c.work) ∧
      Post r (rowBase lanes base inputHead) (readReply params inputHead) c d := by
  obtain ⟨d,H,post⟩:=machine_exec r input c base inputHead hi hc head cursor
  rw [localReply_eq r base inputHead params c.work buffer headBound] at post
  exact ⟨d,H,post⟩

end CatalyticTreeEval.Contracts.NativeInputProbe
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeInputProbeFlags -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeInputProbe

open NativeRoundSupport
open NativeInputInspect (Roles Reply Post rowFootprint replyWork)

/-- The three concrete reply cells encode the returned finite reply, even
when their old contents were arbitrary. Distinct roles are an explicit
layout premise, never an invariant silently assumed by the native code. -/
theorem reply_fields {lanes : ℕ} {A B : Main.Machine} (r : Roles lanes)
    (rowBase : ℕ) (reply : Reply) (c : Config A) (d : Config B)
    (post : Post r rowBase reply c d)
    (hop : r.replyOrigin≠r.replyPresent) (hov : r.replyOrigin≠r.replyValue)
    (hpv : r.replyPresent≠r.replyValue) :
    d.work (rowBase+r.replyOrigin.val)=reply.isOrigin ∧
      d.work (rowBase+r.replyPresent.val)=reply.isPresent ∧
      d.work (rowBase+r.replyValue.val)=reply.value := by
  have ne {x y : Fin lanes} (h : x≠y) : rowBase+x.val≠rowBase+y.val:=by
    intro he
    apply h
    apply Fin.ext
    omega
  rw [post.2.1]
  dsimp only [replyWork]
  exact ⟨by rw [Function.update_of_ne (ne hov),Function.update_of_ne (ne hop),Function.update_self],
    by rw [Function.update_of_ne (ne hpv),Function.update_self],by rw [Function.update_self]⟩

theorem frame_other_lane {lanes : ℕ} {A B : Main.Machine} (r : Roles lanes) (target : Fin lanes)
    (base cursorRow row : ℕ) (c : Config A) (d : Config B)
    (H : Frame (rowFootprint r (base+(lanes+1)*cursorRow)) c d)
    (ho : target≠r.replyOrigin) (hp : target≠r.replyPresent) (hv : target≠r.replyValue) :
    d.work (WorkLanes.address target base row)=c.work (WorkLanes.address target base row) := by
  apply H.1
  intro mem
  simp only [rowFootprint,Set.mem_insert_iff,Set.mem_singleton_iff] at mem
  have reject (other : Fin lanes) (hne : target≠other)
      (eq : WorkLanes.address target base row=base+(lanes+1)*cursorRow+other.val) : False:=by
    exact hne (WorkLanes.address_lanes_injective target other base row cursorRow eq).1
  rcases mem with h|h|h
  · exact reject r.replyOrigin ho h
  · exact reject r.replyPresent hp h
  · exact reject r.replyValue hv h

/-- Under the explicit service-lane layout, the probe preserves the actual
buffer and its sole input-cursor bookmark. These are the next native Move
callback's physical preconditions. -/
theorem buffer_preserved {lanes : ℕ} {A B : Main.Machine} (r : Roles lanes)
    (params : List Bool) (base inputHead : ℕ) (c : Config A) (d : Config B)
    (H : Frame (rowFootprint r (rowBase lanes base inputHead)) c d)
    (buffer : Buffer r base params c.work)
    (readonly : ∀ lane ∈ ({r.origin,r.data,r.bookmark} : Finset (Fin lanes)),
      lane≠r.replyOrigin ∧ lane≠r.replyPresent ∧ lane≠r.replyValue)
    (cursor : ∀ j ≤ inputHead,
      c.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead)) :
    Buffer r base params d.work ∧
      ∀ j ≤ inputHead, d.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead) := by
  have keep (lane : Fin lanes) (mem : lane ∈ ({r.origin,r.data,r.bookmark} : Finset (Fin lanes))) (row : ℕ) :
      d.work (WorkLanes.address lane base row)=c.work (WorkLanes.address lane base row):=by
    obtain ⟨ho,hp,hv⟩:=readonly lane mem
    exact frame_other_lane r lane base (3+3*inputHead) row c d H ho hp hv
  have ko:=keep r.origin (by simp)
  have kd:=keep r.data (by simp)
  have kb:=keep r.bookmark (by simp)
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro row
    rw [ko]
    exact buffer.origin row
  · intro j hj
    rw [kd]
    exact buffer.tags j hj
  · intro j hj
    rw [kd]
    exact buffer.values j hj
  · rw [kd]
    exact buffer.terminator
  · intro j hj
    rw [kb]
    exact cursor j hj

end CatalyticTreeEval.Contracts.NativeInputProbe
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeInputProbeResource -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeInputProbe

open NativeRoundSupport NativeHeadStationary
open NativeInputInspect (Roles rowFootprint)

theorem marker_stationary (head : Head) (direction : CatalyticMatching.General.Move) (padding : ℕ) :
    Stationary head (NativeMarkerSeek.machine direction padding) := by
  intro q input work catalyst io wo co
  cases head <;> dsimp [motion,NativeMarkerSeek.machine] <;> split <;> rfl

theorem locate_stationary {lanes : ℕ} (head : Head) (bookmark : Fin lanes) :
    Stationary head (NativeInputLocate.machine bookmark) :=
  sequential head _ _ (literal head _ _ _) (marker_stationary head _ _)

theorem stationary {lanes : ℕ} (head : Head) (r : Roles lanes) :
    Stationary head (machine r) :=
  sequential head _ _ (locate_stationary head r.bookmark) (NativeInputInspect.stationary head r)

theorem firstExit_envelope {N : Main.Machine} {lanes : ℕ} (r : Roles lanes)
    (input : List Bool) (c : Config N) (d : Config (machine r)) (base inputHead T : ℕ)
    (H : FirstExit ((machine r).step input)
      (fun _ e => e.workHead < bound lanes base inputHead ∧
        Frame (rowFootprint r (rowBase lanes base inputHead)) c e)
      {e | e.state=none} (startOn (machine r) c) d T) :
    FirstExit ((machine r).step input)
      (fun _ e => (Envelope.mk 0 (bound lanes base inputHead) c.catalystHead (c.catalystHead+1)).Contains e ∧
        Frame (rowFootprint r (rowBase lanes base inputHead)) c e)
      {e | e.state=none} (startOn (machine r) c) d T :=
  firstExit_port_envelope input c d T _ _ (stationary .catalyst r) H

theorem bound_le (lanes base inputHead length : ℕ) (H : inputHead ≤ length+1) :
    bound lanes base inputHead ≤ base+(lanes+1)*(8+3*length) := by
  unfold bound
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (lanes+1) (by omega)) base

theorem time_le_buffered {lanes : ℕ} (r : Roles lanes) (base inputHead length : ℕ)
    (work : ℕ → Bool) (H : inputHead ≤ length+1) :
    time r base inputHead work ≤ 20*(lanes+1)*(length+2) :=
  (time_le r base inputHead work).trans (Nat.mul_le_mul_left (20*(lanes+1)) (by omega))

end CatalyticTreeEval.Contracts.NativeInputProbe
end

/- Proof source: Solutions.CatalyticTreeEvaluation.NativeBufferedInputAPI -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeInputProbe

open NativeInputInspect (Roles Post rowFootprint)

/-- Public actual-buffer probe certificate, with decoded physical reply bits,
preserved buffer/cursor and bounds independent of any catalytic suffix. -/
theorem probe_exec {lanes : ℕ} (r : Roles lanes) (input params : List Bool)
    (c : Config (machine r)) (base inputHead : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=base+lanes)
    (headBound : inputHead ≤ params.length+1)
    (cursor : ∀ j ≤ params.length+1,
      c.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead))
    (buffer : Buffer r base params c.work)
    (hop : r.replyOrigin≠r.replyPresent) (hov : r.replyOrigin≠r.replyValue)
    (hpv : r.replyPresent≠r.replyValue)
    (readonly : ∀ lane ∈ ({r.origin,r.data,r.bookmark} : Finset (Fin lanes)),
      lane≠r.replyOrigin ∧ lane≠r.replyPresent ∧ lane≠r.replyValue) :
    ∃ (d : Config (machine r)) (T : ℕ),
      FirstExit ((machine r).step input)
        (fun _ e => (Envelope.mk 0 (base+(lanes+1)*(8+3*params.length)) c.catalystHead (c.catalystHead+1)).Contains e ∧
          SameOutside (rowFootprint r (rowBase lanes base inputHead)) c e)
        {e | e.state=none} {c with state:=some (machine r).start} d T ∧
      T ≤ 20*(lanes+1)*(params.length+2) ∧
      Post r (rowBase lanes base inputHead) (readReply params inputHead) c d ∧
      d.work (rowBase lanes base inputHead+r.replyOrigin.val)=(readReply params inputHead).isOrigin ∧
      d.work (rowBase lanes base inputHead+r.replyPresent.val)=(readReply params inputHead).isPresent ∧
      d.work (rowBase lanes base inputHead+r.replyValue.val)=(readReply params inputHead).value ∧
      Buffer r base params d.work ∧
      (∀ j ≤ params.length+1,
        d.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead)) := by
  obtain ⟨d,H,post⟩:=reads_input r input params c base inputHead hi hc head
    (fun j hj => cursor j (by omega)) buffer headBound
  let T:=time r base inputHead c.work
  have HE:=firstExit_envelope r input c d base inputHead T H
  have Hfinal : NativeRoundSupport.Frame (rowFootprint r (rowBase lanes base inputHead)) c d:=
    (H.during T le_rfl d H.result).2
  obtain ⟨fo,fp,fv⟩:=reply_fields r (rowBase lanes base inputHead) _ c d post hop hov hpv
  obtain ⟨newBuffer,_⟩:=buffer_preserved r params base inputHead c d Hfinal buffer readonly
    (fun j hj => cursor j (by omega))
  refine ⟨d,T,?_,time_le_buffered r base inputHead params.length c.work headBound,post,fo,fp,fv,newBuffer,?_⟩
  · refine {result:=HE.result,exit_mem:=HE.exit_mem,cut:=HE.cut,during:=?_}
    intro u hu e he
    obtain ⟨V,F⟩:=HE.during u hu e he
    change (0 ≤ e.workHead ∧ e.workHead < base+(lanes+1)*(8+3*params.length) ∧
      c.catalystHead ≤ e.catalystHead ∧ e.catalystHead < c.catalystHead+1) ∧ _
    exact ⟨⟨V.1,lt_of_lt_of_le V.2.1 (bound_le lanes base inputHead params.length headBound),
      V.2.2.1,V.2.2.2⟩,F⟩
  · intro j hj
    obtain ⟨ho,hp,hv⟩:=readonly r.bookmark (by simp)
    rw [frame_other_lane r r.bookmark base (3+3*inputHead) (3+3*j) c d Hfinal ho hp hv]
    exact cursor j hj

end CatalyticTreeEval.Contracts.NativeInputProbe
end

open CatalyticTreeEval.Contracts CatalyticTreeEval.Contracts.NativeInputProbe
open CatalyticTreeEval.Contracts.NativeInputInspect (Roles Post rowFootprint)

theorem solution {lanes : ℕ} (r : Roles lanes) (input params : List Bool)
    (c : Config (machine r)) (base inputHead : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=base+lanes)
    (headBound : inputHead ≤ params.length+1)
    (cursor : ∀ j ≤ params.length+1,
      c.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead))
    (buffer : Buffer r base params c.work)
    (hop : r.replyOrigin≠r.replyPresent) (hov : r.replyOrigin≠r.replyValue)
    (hpv : r.replyPresent≠r.replyValue)
    (readonly : ∀ lane ∈ ({r.origin,r.data,r.bookmark} : Finset (Fin lanes)),
      lane≠r.replyOrigin ∧ lane≠r.replyPresent ∧ lane≠r.replyValue) :
    ∃ (d : Config (machine r)) (T : ℕ),
      FirstExit ((machine r).step input)
        (fun _ e => (Envelope.mk 0 (base+(lanes+1)*(8+3*params.length)) c.catalystHead (c.catalystHead+1)).Contains e ∧
          SameOutside (rowFootprint r (rowBase lanes base inputHead)) c e)
        {e | e.state=none} {c with state:=some (machine r).start} d T ∧
      T ≤ 20*(lanes+1)*(params.length+2) ∧
      Post r (rowBase lanes base inputHead) (readReply params inputHead) c d ∧
      d.work (rowBase lanes base inputHead+r.replyOrigin.val)=(readReply params inputHead).isOrigin ∧
      d.work (rowBase lanes base inputHead+r.replyPresent.val)=(readReply params inputHead).isPresent ∧
      d.work (rowBase lanes base inputHead+r.replyValue.val)=(readReply params inputHead).value ∧
      Buffer r base params d.work ∧
      (∀ j ≤ params.length+1,
        d.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead)) := by
  exact probe_exec r input params c base inputHead hi hc head headBound cursor buffer hop hov hpv readonly
