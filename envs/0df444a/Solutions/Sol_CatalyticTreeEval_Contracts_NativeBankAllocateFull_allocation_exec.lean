-- Prove2me | solution 1 for CatalyticTreeEval.Contracts.NativeBankAllocateFull.allocation_exec
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T11:12:19.011776+00:00
-- url     : https://prove2.me/submissions/ce028062-37fb-4a5e-bfd2-3fcacee905a4

import Definitions.Def_CatalyticTreeEval_NativeBankAllocation

/- Proof component: Solutions.CatalyticTreeEvaluation.MachineContractLaws -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.SequentialMachineLaws -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.BranchMachineLaws -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.ReentryMachineLaws -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeRoundSupport -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeVisits -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeFrames -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeLiteral -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.TaggedRewind -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.RippleAdder -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.RippleAdderBank -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.RippleSubtractor -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.RippleSubtractorBank -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.ShiftAppend -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.ShiftAppendBank -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.RestoringDivision -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.RestoringRound -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.RestoringRoundMachine -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeLaneFlagCopy -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeMarkerSeek -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLanes -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneGeometry -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeLaneWordGeometry -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeLaneWordBit -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.WhileFlagLaws -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeLaneWordForward -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeLaneWordRewind -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeMarkerSeekPort -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeOriginSeek -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeMarkerSeek

open NativeRoundSupport
open RestoringRound (SameIO)

theorem left_marker_position (lanes base row p : ℕ) (hp : p ≤ row) :
    NativeLiteral.position .left (WorkLanes.markerAddress lanes base row) (p*(lanes+1)) =
      WorkLanes.markerAddress lanes base (row-p) := by
  rw [NativeLiteral.position_left]
  have hs := Nat.mul_le_mul_right (lanes+1) hp
  have he : (row-p)*(lanes+1)=row*(lanes+1)-p*(lanes+1) := Nat.sub_mul _ _ _
  dsimp [WorkLanes.markerAddress]
  rw [Nat.mul_comm (lanes+1) (row-p),he,Nat.mul_comm (lanes+1) row]
  omega

/-- Actual read-only native return on the immutable origin column. -/
theorem origin_exec {N : Main.Machine} (lanes : ℕ) (input : List Bool) (c : Config N)
    (base row bound : ℕ) (hi : c.inputHead ≤ input.length+1)
    (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=WorkLanes.markerAddress lanes base row)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (hstart : c.workHead < bound) (hend : WorkLanes.markerAddress lanes base 0 < bound) :
    ∃ d : Config (machine .left lanes),
      FirstExit ((machine .left lanes).step input)
        (fun _ e => e.workHead < bound ∧ Frame ⟨∅,∅⟩ c e)
        {e | e.state=none} (startOn (machine .left lanes) c) d (row*(lanes+1)+1) ∧
      d.workHead=WorkLanes.markerAddress lanes base 0 ∧ d.work=c.work ∧ SameIO c d := by
  apply seek_exec .left lanes input c row (WorkLanes.markerAddress lanes base 0) bound hi hc
  · rw [head,left_marker_position lanes base row row le_rfl,Nat.sub_self]
  · exact hstart
  · exact hend
  · intro p hp
    rw [head,left_marker_position lanes base row p (by omega),origin]
    simp [show row-p ≠ 0 by omega]
  · simpa using origin 0

end CatalyticTreeEval.Contracts.NativeMarkerSeek
end

/- Proof component: Solutions.CatalyticTreeEvaluation.BankColumnInitialize -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.BankColumnInitialize

open CatalyticMatching.General

theorem prefix_step (lanes : ℕ) (selected : Finset (Fin lanes))
    (work : ℕ → Bool) (start u : ℕ) :
    Function.update (prefixWork lanes selected work start u) (start + u)
      ((literal lanes selected u).getD (prefixWork lanes selected work start u (start + u))) =
        prefixWork lanes selected work start (u + 1) := by
  funext p
  by_cases hit : p = start + u
  · subst p
    simp only [Function.update_self, prefixWork, lt_self_iff_false, and_false, if_false]
    rw [if_pos (by omega)]
    simp only [Nat.add_sub_cancel_left]
  · rw [Function.update_of_ne hit]
    unfold prefixWork
    by_cases inside : start ≤ p ∧ p < start + u
    · rw [if_pos inside, if_pos (by omega)]
    · rw [if_neg inside, if_neg (by omega)]

theorem step_snapshot (lanes : ℕ) (selected : Finset (Fin lanes)) (input : List Bool)
    (c : Config (machine lanes selected)) (u : ℕ) (hu : u < steps lanes)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    (machine lanes selected).step input (snapshot lanes selected c u) =
      some (snapshot lanes selected c (u + 1)) := by
  simp [Machine.step, machine, snapshot, hu, Move.apply, hi, hc,
    prefix_step, Nat.add_assoc]

theorem run_snapshot (lanes : ℕ) (selected : Finset (Fin lanes)) (input : List Bool)
    (c : Config (machine lanes selected))
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    ∀ u ≤ steps lanes,
      runFrom ((machine lanes selected).step input) (snapshot lanes selected c 0) u =
        some (snapshot lanes selected c u) := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
      intro hu
      rw [runFrom_succ, ih (by omega), Option.bind_some]
      exact step_snapshot lanes selected input c u (by omega) hi hc

theorem prefix_frame (lanes : ℕ) (selected : Finset (Fin lanes))
    (work : ℕ → Bool) (start u : ℕ) (hu : u ≤ steps lanes) (p : ℕ)
    (hp : p ∉ (footprint lanes selected start).work) :
    prefixWork lanes selected work start u p = work p := by
  by_cases inside : start ≤ p ∧ p < start + u
  · cases value : literal lanes selected (p - start) with
    | none => simp only [prefixWork, if_pos inside, value, Option.getD_none]
    | some bit =>
        apply False.elim
        apply hp
        exact ⟨inside.1, by omega, by simp only [value, Option.isSome_some]⟩
  · simp only [prefixWork, if_neg inside]

/-- A real fixed native sweep writes only selected operand tag/A/B cells.
All input, catalyst and output data are preserved at every intermediate step. -/
theorem firstExit (lanes : ℕ) (selected : Finset (Fin lanes)) (input : List Bool)
    (c : Config (machine lanes selected))
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    FirstExit ((machine lanes selected).step input)
      (fun _ d => (Envelope.mk c.workHead (c.workHead + steps lanes + 1)
        c.catalystHead (c.catalystHead + 1)).Contains d ∧
        SameOutside (footprint lanes selected c.workHead) c d)
      {d | d.state = none} (snapshot lanes selected c 0)
      (snapshot lanes selected c (steps lanes)) (steps lanes) where
  result := run_snapshot lanes selected input c hi hc _ le_rfl
  during u hu d hd := by
    rw [run_snapshot lanes selected input c hi hc u hu] at hd
    cases Option.some.inj hd
    constructor
    · dsimp [Envelope.Contains, snapshot]
      omega
    · exact ⟨prefix_frame lanes selected c.work c.workHead u hu, rfl, fun _ _ => rfl⟩
  exit_mem := by simp [snapshot]
  cut u hu d hd := by
    rw [run_snapshot lanes selected input c hi hc u (by omega)] at hd
    cases Option.some.inj hd
    simp [snapshot, hu]

end CatalyticTreeEval.Contracts.BankColumnInitialize
end

/- Proof component: Solutions.CatalyticTreeEvaluation.BankColumnInitializeLanes -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BankColumnInitialize

theorem literal_selected {lanes : ℕ} (selected : Finset (Fin lanes)) (lane : Fin lanes)
    (phase : ℕ) (residue : phase % (lanes + 1) = lane.val) (member : lane ∈ selected) :
    literal lanes selected phase = some (decide (phase < lanes + 1)) := by
  have small : phase % (lanes + 1) < lanes := by rw [residue]; exact lane.isLt
  unfold literal
  rw [dif_pos small]
  have equal : (⟨phase % (lanes + 1), small⟩ : Fin lanes) = lane := by
    apply Fin.ext
    exact residue
  rw [equal, if_pos member]

theorem literal_unselected {lanes : ℕ} (selected : Finset (Fin lanes)) (lane : Fin lanes)
    (phase : ℕ) (residue : phase % (lanes + 1) = lane.val) (member : lane ∉ selected) :
    literal lanes selected phase = none := by
  have small : phase % (lanes + 1) < lanes := by rw [residue]; exact lane.isLt
  unfold literal
  rw [dif_pos small]
  have equal : (⟨phase % (lanes + 1), small⟩ : Fin lanes) = lane := by
    apply Fin.ext
    exact residue
  rw [equal, if_neg member]

theorem literal_origin (lanes : ℕ) (selected : Finset (Fin lanes)) (phase : ℕ)
    (residue : phase % (lanes + 1) = lanes) : literal lanes selected phase = none := by
  simp [literal, residue]

/-- Physical row subtraction keeps the column residue whenever the target
cell lies on or after the sweep's row start. -/
theorem offset_mod (lanes base first row column : ℕ) (columnBound : column < lanes + 1)
    (afterStart : base + (lanes + 1) * first ≤ base + (lanes + 1) * row + column) :
    (base + (lanes + 1) * row + column - (base + (lanes + 1) * first)) %
      (lanes + 1) = column := by
  have rows : first ≤ row := by
    by_contra notRows
    have scaled := Nat.mul_le_mul_left (lanes + 1) (show row + 1 ≤ first by omega)
    simp only [Nat.mul_add, Nat.mul_one] at scaled
    omega
  have scaled := Nat.mul_le_mul_left (lanes + 1) rows
  have difference : base + (lanes + 1) * row + column - (base + (lanes + 1) * first) =
      (lanes + 1) * (row - first) + column := by
    rw [Nat.mul_sub_left_distrib]
    omega
  rw [difference]
  simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt columnBound]

theorem prefix_unselected {lanes : ℕ} (selected : Finset (Fin lanes))
    (lane : Fin lanes) (member : lane ∉ selected) (base first row elapsed : ℕ)
    (work : ℕ → Bool) :
    prefixWork lanes selected work (base + (lanes + 1) * first) elapsed
      (WorkLanes.address lane base row) = work (WorkLanes.address lane base row) := by
  by_cases inside : base + (lanes + 1) * first ≤ WorkLanes.address lane base row ∧
      WorkLanes.address lane base row < base + (lanes + 1) * first + elapsed
  · have residue := offset_mod lanes base first row lane.val (by omega) inside.1
    have unchanged := literal_unselected selected lane
      (WorkLanes.address lane base row - (base + (lanes + 1) * first)) residue member
    simp only [prefixWork, if_pos inside, unchanged, Option.getD_none]
  · simp only [prefixWork, if_neg inside]

theorem prefix_origin (lanes : ℕ) (selected : Finset (Fin lanes))
    (base first elapsed : ℕ) (work : ℕ → Bool) (origin : WorkLanes.OriginTrack lanes base work) :
    WorkLanes.OriginTrack lanes base
      (prefixWork lanes selected work (base + (lanes + 1) * first) elapsed) := by
  intro row
  by_cases inside : base + (lanes + 1) * first ≤ WorkLanes.markerAddress lanes base row ∧
      WorkLanes.markerAddress lanes base row < base + (lanes + 1) * first + elapsed
  · have residue := offset_mod lanes base first row lanes (by omega) inside.1
    have unchanged := literal_origin lanes selected
      (WorkLanes.markerAddress lanes base row - (base + (lanes + 1) * first)) residue
    simpa only [prefixWork, if_pos inside, unchanged, Option.getD_none] using origin row
  · simpa only [prefixWork, if_neg inside] using origin row

/-- At the three selected offsets the actual sweep writes true, false, false.
This statement uses the physical start directly, without a hidden row address. -/
theorem finished_selected {lanes : ℕ} (selected : Finset (Fin lanes))
    (lane : Fin lanes) (member : lane ∈ selected)
    (c : Config (machine lanes selected)) (row : Fin 3) :
    (snapshot lanes selected c (steps lanes)).work
      (c.workHead + ((lanes + 1) * row.val + lane.val)) = decide (row.val = 0) := by
  let phase := (lanes + 1) * row.val + lane.val
  have laneBound : lane.val < lanes + 1 := by omega
  have phaseBound : phase < steps lanes := by
    have scaled := Nat.mul_le_mul_left (lanes + 1) (show row.val + 1 ≤ 3 by omega)
    simp only [Nat.mul_add, Nat.mul_one] at scaled
    dsimp [phase, steps]
    omega
  have residue : phase % (lanes + 1) = lane.val := by
    simp [phase, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt laneBound]
  have wrote := literal_selected selected lane phase residue member
  change prefixWork lanes selected c.work c.workHead (steps lanes) (c.workHead + phase) = _
  have inside : c.workHead ≤ c.workHead + phase ∧
      c.workHead + phase < c.workHead + steps lanes := by omega
  simp only [prefixWork, if_pos inside, Nat.add_sub_cancel_left, wrote, Option.getD_some]
  by_cases zero : row.val = 0
  · have small : phase < lanes + 1 := by simpa only [phase, zero, Nat.mul_zero, Nat.zero_add] using laneBound
    simp only [zero, small, decide_true]
  · have large : ¬phase < lanes + 1 := by
      have scaled := Nat.mul_le_mul_left (lanes + 1) (show 1 ≤ row.val by omega)
      simp only [Nat.mul_one] at scaled
      dsimp [phase]
      omega
    simp only [zero, large, decide_false]

theorem finished_tag {lanes : ℕ} (selected : Finset (Fin lanes))
    (lane : Fin lanes) (member : lane ∈ selected) (c : Config (machine lanes selected)) :
    (snapshot lanes selected c (steps lanes)).work (c.workHead + lane.val) = true := by
  simpa using finished_selected selected lane member c (0 : Fin 3)

theorem finished_A {lanes : ℕ} (selected : Finset (Fin lanes))
    (lane : Fin lanes) (member : lane ∈ selected) (c : Config (machine lanes selected)) :
    (snapshot lanes selected c (steps lanes)).work (c.workHead + (lanes + 1) + lane.val) = false := by
  simpa only [Fin.val_one, Nat.mul_one, Nat.add_assoc, Nat.one_ne_zero, decide_false] using
    finished_selected selected lane member c (1 : Fin 3)

theorem finished_B {lanes : ℕ} (selected : Finset (Fin lanes))
    (lane : Fin lanes) (member : lane ∈ selected) (c : Config (machine lanes selected)) :
    (snapshot lanes selected c (steps lanes)).work (c.workHead + 2 * (lanes + 1) + lane.val) = false := by
  simpa [Nat.mul_comm, Nat.add_assoc] using finished_selected selected lane member c (2 : Fin 3)

end CatalyticTreeEval.Contracts.BankColumnInitialize
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBankAllocateWork -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeBankAllocate

/-- The exact non-counter-lane tape after each allocation iteration. -/
def columnsWork {lanes : ℕ} (bookmark : Fin lanes) (selected : Finset (Fin lanes))
    (base : ℕ) (work : ℕ → Bool) : ℕ → ℕ → Bool
  | 0 => work
  | n+1 => advanceWork bookmark selected base (6+3*n) (columnsWork bookmark selected base work n)

theorem advanceWork_congr_point {lanes : ℕ} (bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (base row p : ℕ) (work work' : ℕ → Bool)
    (same : work p = work' p) :
    advanceWork bookmark selected base row work p = advanceWork bookmark selected base row work' p := by
  simp only [advanceWork,Function.update_apply,BankColumnInitialize.prefixWork]
  split_ifs <;> simp_all

theorem update_origin {lanes : ℕ} (lane : Fin lanes) (base row : ℕ)
    (work : ℕ → Bool) (bit : Bool) (origin : WorkLanes.OriginTrack lanes base work) :
    WorkLanes.OriginTrack lanes base (Function.update work (WorkLanes.address lane base row) bit) := by
  intro p
  rw [Function.update_of_ne (WorkLanes.address_ne_marker lane base row p).symm]
  exact origin p

theorem advance_origin {lanes : ℕ} (bookmark : Fin lanes) (selected : Finset (Fin lanes))
    (base row : ℕ) (work : ℕ → Bool) (origin : WorkLanes.OriginTrack lanes base work) :
    WorkLanes.OriginTrack lanes base (advanceWork bookmark selected base row work) := by
  apply update_origin
  exact BankColumnInitialize.prefix_origin lanes selected base row _ _
    (update_origin bookmark base row work false origin)

/-- Moving the single actual bookmark creates exactly the next bookmark;
this is a tape invariant, not a numeric address held in finite control. -/
theorem advance_bookmark {lanes : ℕ} (bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : bookmark ∉ selected)
    (base row : ℕ) (work : ℕ → Bool)
    (unique : ∀ p, work (WorkLanes.address bookmark base p) = decide (p = row)) :
    ∀ p, advanceWork bookmark selected base row work (WorkLanes.address bookmark base p) =
      decide (p = row + 3) := by
  intro p
  by_cases next : p = row + 3
  · subst p
    simp [advanceWork]
  have hn : WorkLanes.address bookmark base p ≠ WorkLanes.address bookmark base (row + 3) :=
    fun he => next (WorkLanes.address_injective bookmark base he)
  rw [advanceWork, Function.update_of_ne hn,
    BankColumnInitialize.prefix_unselected selected bookmark notSelected]
  by_cases old : p = row
  · subst p
    simp only [Function.update_self]
    simp [show row ≠ row + 3 by omega]
  have ho : WorkLanes.address bookmark base p ≠ WorkLanes.address bookmark base row :=
    fun he => old (WorkLanes.address_injective bookmark base he)
  rw [Function.update_of_ne ho, unique]
  simp [old, next]

theorem advance_inactive {lanes : ℕ} (bookmark other : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : other ∉ selected)
    (notBookmark : other ≠ bookmark) (base row : ℕ) (work : ℕ → Bool) (p : ℕ) :
    advanceWork bookmark selected base row work (WorkLanes.address other base p) =
      work (WorkLanes.address other base p) := by
  have hn (q : ℕ) : WorkLanes.address other base p ≠ WorkLanes.address bookmark base q := by
    intro he
    exact notBookmark (WorkLanes.address_lanes_injective other bookmark base _ _ he).1
  rw [advanceWork, Function.update_of_ne (hn _),
    BankColumnInitialize.prefix_unselected selected other notSelected,
    Function.update_of_ne (hn _)]

/-- Each initialized column has the actual tag/A/B bits true/false/false. -/
theorem advance_selected {lanes : ℕ} (bookmark lane : Fin lanes)
    (selected : Finset (Fin lanes)) (member : lane ∈ selected)
    (notBookmark : lane ≠ bookmark) (base row : ℕ) (work : ℕ → Bool) (off : Fin 3) :
    advanceWork bookmark selected base row work (WorkLanes.address lane base (row + off.val)) =
      decide (off.val = 0) := by
  have hn : WorkLanes.address lane base (row + off.val) ≠
      WorkLanes.address bookmark base (row + 3) := by
    intro he
    exact notBookmark (WorkLanes.address_lanes_injective lane bookmark base _ _ he).1
  rw [advanceWork, Function.update_of_ne hn]
  let c : Config (BankColumnInitialize.machine lanes selected) :=
    { (BankColumnInitialize.machine lanes selected).initial [] with
      workHead := base + (lanes + 1) * row
      work := Function.update work (WorkLanes.address bookmark base row) false }
  have ht := BankColumnInitialize.finished_selected selected lane member c off
  have hp : WorkLanes.address lane base (row + off.val) =
      (base + (lanes + 1) * row) + ((lanes + 1) * off.val + lane.val) := by
    dsimp [WorkLanes.address]
    ring
  rw [hp]
  exact ht

end CatalyticTreeEval.Contracts.NativeBankAllocate
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeLiteralWritePort -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeFramedComposition -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBookmarkHome -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace CatalyticTreeEval.Contracts.NativeBookmarkHome

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

/-- From the actual bookmark cell, return to the counter flag without changing
any data, charging both fixed hops and the complete origin search. -/
theorem machine_exec {N : Main.Machine} {lanes : ℕ} (counter bookmark : Fin lanes)
    (input : List Bool) (c : Config N) (base row : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=WorkLanes.address bookmark base row)
    (origin : WorkLanes.OriginTrack lanes base c.work) :
    ∃ d : Config (machine counter bookmark),
      FirstExit ((machine counter bookmark).step input)
        (fun _ e => e.workHead < base+(lanes+1)*(row+1) ∧ Frame ⟨∅,∅⟩ c e)
        {e | e.state=none} (startOn (machine counter bookmark) c) d (time counter bookmark row) ∧
      d.workHead=WorkLanes.address counter base 0 ∧ d.work=c.work ∧ SameIO c d := by
  let A:=NativeBankAllocate.originStart bookmark
  let B:=NativeBankAllocate.originHome lanes
  let C:=NativeBankAllocate.counterFlag counter
  let bound:=base+(lanes+1)*(row+1)
  have addr (lane : Fin lanes) (p : ℕ) (hp : p < row+1) : WorkLanes.address lane base p < bound :=
    WorkLanes.address_lt_prefix lane base p _ hp
  have mark (p : ℕ) (hp : p < row+1) : WorkLanes.markerAddress lanes base p < bound :=
    WorkLanes.marker_lt_prefix lanes base p _ hp
  obtain ⟨d1,H1,h1h,h1w,h1IO⟩ := NativeLaneWordTransfer.move_exec .right (lanes-bookmark.val)
    input c (WorkLanes.markerAddress lanes base row) bound hi hc
    (by rw [NativeLiteral.position_right,head]; dsimp [WorkLanes.address,WorkLanes.markerAddress]; omega)
    (by rw [head];exact addr bookmark row (by omega)) (mark row (by omega))
  have hi1 : d1.inputHead ≤ input.length+1 := by rw [h1IO.1];exact hi
  have hc1 : d1.catalystHead ≤ d1.catalyst.length := by rw [h1IO.2.1,h1IO.2.2.1];exact hc
  obtain ⟨d2,H2,h2h,h2w,h2IO⟩ := NativeMarkerSeek.origin_exec lanes input d1 base row bound hi1 hc1 h1h
    (by rw [h1w];exact origin) (by rw [h1h];exact mark row (by omega)) (mark 0 (by omega))
  have io2:=sameIO_trans h1IO h2IO
  have hi2 : d2.inputHead ≤ input.length+1 := by rw [io2.1];exact hi
  have hc2 : d2.catalystHead ≤ d2.catalyst.length := by rw [io2.2.1,io2.2.2.1];exact hc
  obtain ⟨d3,H3,h3h,h3w,h3IO⟩ := NativeLaneWordTransfer.move_exec .left (lanes-counter.val)
    input d2 (WorkLanes.address counter base 0) bound hi2 hc2
    (by rw [NativeLiteral.position_left,h2h]; dsimp [WorkLanes.address,WorkLanes.markerAddress];omega)
    (by rw [h2h];exact mark 0 (by omega)) (addr counter 0 (by omega))
  have H23:=framed_seq B C input d1 d2 d3 (row*(lanes+1)+1) (lanes-counter.val+1) bound ⟨∅,∅⟩ H2 H3
  let e:=Sequential.rightConfig B C d3
  have H:=framed_seq A (Sequential.machine B C) input c d1 e (lanes-bookmark.val+1)
    ((row*(lanes+1)+1)+(lanes-counter.val+1)) bound ⟨∅,∅⟩ H1 H23
  let d:=Sequential.rightConfig A (Sequential.machine B C) e
  refine ⟨d,H,h3h,?_,sameIO_trans io2 h3IO⟩
  change d3.work=c.work
  rw [h3w,h2w,h1w]

/-- Erase only the bookmark before returning; this is the charged final cleanup
used after allocation and after printer-replay callbacks. -/
theorem clear_exec {N : Main.Machine} {lanes : ℕ} (counter bookmark : Fin lanes)
    (input : List Bool) (c : Config N) (base row : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=WorkLanes.address bookmark base row)
    (origin : WorkLanes.OriginTrack lanes base c.work) :
    ∃ d : Config (clear counter bookmark),
      FirstExit ((clear counter bookmark).step input)
        (fun _ e => e.workHead < base+(lanes+1)*(row+1) ∧
          Frame ⟨{WorkLanes.address bookmark base row},∅⟩ c e)
        {e | e.state=none} (startOn (clear counter bookmark) c) d (1+time counter bookmark row) ∧
      d.workHead=WorkLanes.address counter base 0 ∧
      d.work=Function.update c.work (WorkLanes.address bookmark base row) false ∧ SameIO c d := by
  let A:=NativeBankAllocate.clearBookmark
  let B:=machine counter bookmark
  let bound:=base+(lanes+1)*(row+1)
  let F : Footprint:=⟨{WorkLanes.address bookmark base row},∅⟩
  obtain ⟨d1,H1,h1h,h1w,h1IO⟩ := NativeLiteral.write_exec .stay 0 false input c
    (WorkLanes.address bookmark base row) bound hi hc
    (by simpa only [NativeLiteral.position] using head)
    (by rw [head];exact WorkLanes.address_lt_prefix bookmark base row _ (by omega))
    (WorkLanes.address_lt_prefix bookmark base row _ (by omega))
  have hi1 : d1.inputHead ≤ input.length+1 := by rw [h1IO.1];exact hi
  have hc1 : d1.catalystHead ≤ d1.catalyst.length := by rw [h1IO.2.1,h1IO.2.2.1];exact hc
  obtain ⟨d2,H2,h2h,h2w,h2IO⟩ := machine_exec counter bookmark input d1 base row hi1 hc1 h1h
    (by rw [h1w];exact NativeBankAllocate.update_origin bookmark base row c.work false origin)
  have H2f:=firstExit_mono input d1 _ _ _ _ _ _ F H2 le_rfl (by simp) (by simp)
  have H:=framed_seq A B input c d1 d2 1 (time counter bookmark row) bound F H1 H2f
  let d:=Sequential.rightConfig A B d2
  refine ⟨d,H,h2h,?_,sameIO_trans h1IO h2IO⟩
  change d2.work=_
  rw [h2w,h1w]

end CatalyticTreeEval.Contracts.NativeBookmarkHome
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeMSBFoldMoves -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeMSBFold

open NativeRoundSupport
open RestoringRound (SameIO)

theorem moveFlag_exec {N : Main.Machine} {lanes : ℕ} (fromLane toLane : Fin lanes)
    (input : List Bool) (c : Config N) (base : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base + fromLane.val) :
    ∃ d : Config (moveFlag fromLane toLane),
      FirstExit ((moveFlag fromLane toLane).step input)
        (fun _ e => e.workHead < base + lanes ∧ Frame ⟨∅,∅⟩ c e) {d | d.state = none}
        (startOn (moveFlag fromLane toLane) c) d (NativeLaneFlagCopy.distance fromLane toLane + 1) ∧
      d.workHead = base + toLane.val ∧ d.work = c.work ∧ SameIO c d := by
  let cc := startOn (moveFlag fromLane toLane) c
  let d := NativeLiteral.finished (NativeLaneFlagCopy.forward fromLane toLane)
    (NativeLaneFlagCopy.distance fromLane toLane) none cc
  have H0 := NativeLiteral.firstExit (NativeLaneFlagCopy.forward fromLane toLane)
    (NativeLaneFlagCopy.distance fromLane toLane) none input cc hi hc
  have H : FirstExit ((moveFlag fromLane toLane).step input) (fun _ _ => True) {d | d.state = none}
      cc d (NativeLaneFlagCopy.distance fromLane toLane + 1) := by
    simpa [moveFlag, cc, d, NativeLiteral.live, startOn, NativeLiteral.machine,
      NativeLiteral.position] using forget H0
  have V := NativeLaneFlagCopy.literal_visits (NativeLaneFlagCopy.forward fromLane toLane)
    (NativeLaneFlagCopy.distance fromLane toLane) none input c (base + lanes) hi hc (by omega)
    (by rw [hhead, NativeLaneFlagCopy.forward_position]; omega)
  have F := NativeLaneFlagCopy.literal_none_frames (NativeLaneFlagCopy.forward fromLane toLane)
    (NativeLaneFlagCopy.distance fromLane toLane) input c hi hc
  have HF : FirstExit ((moveFlag fromLane toLane).step input)
      (fun _ e => e.workHead < base + lanes ∧ Frame ⟨∅,∅⟩ c e) {d | d.state = none}
      (startOn (moveFlag fromLane toLane) c) d (NativeLaneFlagCopy.distance fromLane toLane + 1) :=
    { result := H.result
      during := fun u hu e he => ⟨V u hu e he, F u hu e he⟩
      exit_mem := H.exit_mem
      cut := H.cut }
  refine ⟨d, HF, ?_, ?_, ⟨rfl,rfl,rfl,rfl⟩⟩
  · simp [d, cc, NativeLiteral.finished, startOn, hhead, NativeLaneFlagCopy.forward_position]
  · simp [d, cc, NativeLiteral.finished, startOn, Function.update_eq_self]

end CatalyticTreeEval.Contracts.NativeMSBFold
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBookmarkInitialize -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CatalyticTreeEval.Contracts.NativeBookmarkHome

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

/-- Seed the first allocation bookmark using fixed code and return to the
counter. All other data, including already captured counter banks, are framed. -/
theorem seed_exec {N : Main.Machine} {lanes : ℕ} (counter bookmark : Fin lanes)
    (input : List Bool) (c : Config N) (base : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=WorkLanes.address counter base 0)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (blank : ∀ p, c.work (WorkLanes.address bookmark base p)=false) :
    ∃ d : Config (seed counter bookmark),
      FirstExit ((seed counter bookmark).step input)
        (fun _ e => e.workHead < base+(lanes+1)*7 ∧ Frame ⟨{WorkLanes.address bookmark base 6},∅⟩ c e)
        {e | e.state=none} (startOn (seed counter bookmark) c) d
        ((NativeLaneFlagCopy.distance counter bookmark+1)+((6*(lanes+1)+1)+time counter bookmark 6)) ∧
      d.workHead=WorkLanes.address counter base 0 ∧
      d.work=Function.update c.work (WorkLanes.address bookmark base 6) true ∧
      WorkLanes.OriginTrack lanes base d.work ∧
      (∀ p, d.work (WorkLanes.address bookmark base p)=decide (p=6)) ∧ SameIO c d := by
  let A:=NativeBankAllocate.toBookmark counter bookmark
  let B:=NativeLiteral.machine .right (6*(lanes+1)) (some true)
  let C:=machine counter bookmark
  let bound:=base+(lanes+1)*7
  let F : Footprint:=⟨{WorkLanes.address bookmark base 6},∅⟩
  obtain ⟨d1,H1,h1h,h1w,h1IO⟩ := NativeMSBFold.moveFlag_exec counter bookmark input c base hi hc
    (by simpa [WorkLanes.address] using head)
  have H1f:=firstExit_mono input c _ _ _ _ bound _ F H1
    (by have H:=WorkLanes.marker_lt_prefix lanes base 0 7 (by omega);dsimp [WorkLanes.markerAddress] at H;omega)
    (by simp) (by simp)
  have hi1 : d1.inputHead ≤ input.length+1 := by rw [h1IO.1];exact hi
  have hc1 : d1.catalystHead ≤ d1.catalyst.length := by rw [h1IO.2.1,h1IO.2.2.1];exact hc
  obtain ⟨d2,H2,h2h,h2w,h2IO⟩ := NativeLiteral.write_exec .right (6*(lanes+1)) true input d1
    (WorkLanes.address bookmark base 6) bound hi1 hc1
    (by rw [NativeLiteral.position_right,h1h];dsimp [WorkLanes.address];ring)
    (by rw [h1h];simpa only [WorkLanes.address,Nat.mul_zero,Nat.add_zero,bound] using WorkLanes.address_lt_prefix bookmark base 0 7 (by omega))
    (WorkLanes.address_lt_prefix bookmark base 6 7 (by omega))
  have io2:=sameIO_trans h1IO h2IO
  have hi2 : d2.inputHead ≤ input.length+1 := by rw [io2.1];exact hi
  have hc2 : d2.catalystHead ≤ d2.catalyst.length := by rw [io2.2.1,io2.2.2.1];exact hc
  have origin2 : WorkLanes.OriginTrack lanes base d2.work := by
    rw [h2w,h1w]
    exact NativeBankAllocate.update_origin bookmark base 6 c.work true origin
  obtain ⟨d3,H3,h3h,h3w,h3IO⟩ := machine_exec counter bookmark input d2 base 6 hi2 hc2 h2h origin2
  have H3f:=firstExit_mono input d2 _ _ _ _ _ _ F H3 le_rfl (by simp) (by simp)
  have H23:=framed_seq B C input d1 d2 d3 (6*(lanes+1)+1) (time counter bookmark 6) bound F H2 H3f
  let e:=Sequential.rightConfig B C d3
  have H:=framed_seq A (Sequential.machine B C) input c d1 e (NativeLaneFlagCopy.distance counter bookmark+1)
    ((6*(lanes+1)+1)+time counter bookmark 6) bound F H1f H23
  let d:=Sequential.rightConfig A (Sequential.machine B C) e
  have hw : d.work=Function.update c.work (WorkLanes.address bookmark base 6) true := by
    change d3.work=_
    rw [h3w,h2w,h1w]
  refine ⟨d,H,h3h,hw,?_,?_,sameIO_trans io2 h3IO⟩
  · rw [hw]
    exact NativeBankAllocate.update_origin bookmark base 6 c.work true origin
  · intro p
    rw [hw]
    by_cases hit : p=6
    · subst p
      simp
    · rw [Function.update_of_ne (fun he => hit (WorkLanes.address_injective bookmark base he)),blank]
      simp [hit]

/-- Find the unique runtime bookmark, erase it and return to the counter.
This consumes no implicit saved address and leaves the entire bookmark lane blank. -/
theorem cleanup_exec {N : Main.Machine} {lanes : ℕ} (counter bookmark : Fin lanes)
    (input : List Bool) (c : Config N) (base row : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=WorkLanes.address counter base 0)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (unique : ∀ p, c.work (WorkLanes.address bookmark base p)=decide (p=row)) :
    ∃ d : Config (cleanup counter bookmark),
      FirstExit ((cleanup counter bookmark).step input)
        (fun _ e => e.workHead < base+(lanes+1)*(row+1) ∧
          Frame ⟨{WorkLanes.address bookmark base row},∅⟩ c e)
        {e | e.state=none} (startOn (cleanup counter bookmark) c) d
        ((NativeLaneFlagCopy.distance counter bookmark+1)+((row*(lanes+1)+1)+(1+time counter bookmark row))) ∧
      d.workHead=WorkLanes.address counter base 0 ∧
      d.work=Function.update c.work (WorkLanes.address bookmark base row) false ∧
      WorkLanes.OriginTrack lanes base d.work ∧
      (∀ p, d.work (WorkLanes.address bookmark base p)=false) ∧ SameIO c d := by
  let A:=NativeBankAllocate.toBookmark counter bookmark
  let B:=NativeBankAllocate.findBookmark lanes
  let C:=clear counter bookmark
  let bound:=base+(lanes+1)*(row+1)
  let F : Footprint:=⟨{WorkLanes.address bookmark base row},∅⟩
  obtain ⟨d1,H1,h1h,h1w,h1IO⟩ := NativeMSBFold.moveFlag_exec counter bookmark input c base hi hc
    (by simpa [WorkLanes.address] using head)
  have H1f:=firstExit_mono input c _ _ _ _ bound _ F H1
    (by have H:=WorkLanes.marker_lt_prefix lanes base 0 (row+1) (by omega);dsimp [WorkLanes.markerAddress] at H;omega)
    (by simp) (by simp)
  have hi1 : d1.inputHead ≤ input.length+1 := by rw [h1IO.1];exact hi
  have hc1 : d1.catalystHead ≤ d1.catalyst.length := by rw [h1IO.2.1,h1IO.2.2.1];exact hc
  have hp (p : ℕ) : NativeLiteral.position .right d1.workHead (p*(lanes+1))=
      WorkLanes.address bookmark base p := by
    rw [NativeLiteral.position_right,h1h]
    dsimp [WorkLanes.address]
    ring
  obtain ⟨d2,H2,h2h,h2w,h2IO⟩ := NativeMarkerSeek.seek_exec .right lanes input d1 row
    (WorkLanes.address bookmark base row) bound hi1 hc1 (hp row)
    (by rw [h1h];simpa only [WorkLanes.address,Nat.mul_zero,Nat.add_zero,bound] using WorkLanes.address_lt_prefix bookmark base 0 (row+1) (by omega))
    (WorkLanes.address_lt_prefix bookmark base row (row+1) (by omega))
    (by intro p hpr;rw [hp p,h1w,unique];simp [show p ≠ row by omega])
    (by rw [h1w,unique];simp)
  have H2f:=firstExit_mono input d1 _ _ _ _ _ _ F H2 le_rfl (by simp) (by simp)
  have io2:=sameIO_trans h1IO h2IO
  have hi2 : d2.inputHead ≤ input.length+1 := by rw [io2.1];exact hi
  have hc2 : d2.catalystHead ≤ d2.catalyst.length := by rw [io2.2.1,io2.2.2.1];exact hc
  obtain ⟨d3,H3,h3h,h3w,h3IO⟩ := clear_exec counter bookmark input d2 base row hi2 hc2 h2h
    (by rw [h2w,h1w];exact origin)
  have H23:=framed_seq B C input d1 d2 d3 (row*(lanes+1)+1) (1+time counter bookmark row) bound F H2f H3
  let e:=Sequential.rightConfig B C d3
  have H:=framed_seq A (Sequential.machine B C) input c d1 e (NativeLaneFlagCopy.distance counter bookmark+1)
    ((row*(lanes+1)+1)+(1+time counter bookmark row)) bound F H1f H23
  let d:=Sequential.rightConfig A (Sequential.machine B C) e
  have hw : d.work=Function.update c.work (WorkLanes.address bookmark base row) false := by
    change d3.work=_
    rw [h3w,h2w,h1w]
  refine ⟨d,H,h3h,hw,?_,?_,sameIO_trans io2 h3IO⟩
  · rw [hw]
    exact NativeBankAllocate.update_origin bookmark base row c.work false origin
  · intro p
    rw [hw]
    by_cases hit : p=row
    · subst p
      simp
    · rw [Function.update_of_ne (fun he => hit (WorkLanes.address_injective bookmark base he)),unique]
      simp [hit]

end CatalyticTreeEval.Contracts.NativeBookmarkHome
end

/- Proof component: Solutions.CatalyticTreeEvaluation.BankColumnInitializePort -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.BankColumnInitialize

open NativeRoundSupport
open RestoringRound (SameIO)

/-- Native caller port for the fixed three-row sweep. The runtime head supplies
its location; the transition table has no base, row or width parameter. -/
theorem column_exec {N : Main.Machine} (lanes : ℕ) (selected : Finset (Fin lanes))
    (input : List Bool) (c : Config N) (bound : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hend : c.workHead + steps lanes < bound) :
    ∃ d : Config (machine lanes selected),
      FirstExit ((machine lanes selected).step input)
        (fun _ e => e.workHead < bound ∧ Frame (footprint lanes selected c.workHead) c e)
        {e | e.state = none} (startOn (machine lanes selected) c) d (steps lanes) ∧
      d.workHead = c.workHead + steps lanes ∧
      d.work = prefixWork lanes selected c.work c.workHead (steps lanes) ∧ SameIO c d := by
  let cc := startOn (machine lanes selected) c
  let d := snapshot lanes selected cc (steps lanes)
  have H0 := firstExit lanes selected input cc hi hc
  have positive : 0 < steps lanes := by dsimp [steps]; omega
  have zeroWork : prefixWork lanes selected cc.work cc.workHead 0 = cc.work := by
    funext p
    exact if_neg (by omega)
  have entry : snapshot lanes selected cc 0 = cc := by
    simp only [snapshot, dif_pos positive, zeroWork, Nat.add_zero]
    rfl
  rw [entry] at H0
  refine ⟨d,?_,rfl,rfl,⟨rfl,rfl,rfl,rfl⟩⟩
  exact { result := H0.result
          during := by
            intro u hu e he
            have h := H0.during u hu e he
            have hh : e.workHead < c.workHead + steps lanes + 1 := h.1.2.1
            exact ⟨by omega, h.2⟩
          exit_mem := H0.exit_mem
          cut := H0.cut }

end CatalyticTreeEval.Contracts.BankColumnInitialize
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBankAllocateAdvance -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace CatalyticTreeEval.Contracts.NativeBankAllocate

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

/-- One real allocator iteration before its binary countdown: find the single
bookmark, clear it, sweep one tag/A/B column across the selected fixed lanes,
mark the next column, and return through the immutable origin track. Every
movement and write is charged; row appears in the contract only. -/
theorem advance_exec {N : Main.Machine} {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : bookmark ∉ selected)
    (input : List Bool) (c : Config N) (base row : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = WorkLanes.address counter base 0)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (unique : ∀ p, c.work (WorkLanes.address bookmark base p) = decide (p = row)) :
    ∃ d : Config (advance counter bookmark selected),
      FirstExit ((advance counter bookmark selected).step input)
        (fun _ e => e.workHead < base+(lanes+1)*(row+4) ∧
          Frame (advanceFootprint lanes base row) c e)
        {e | e.state=none} (startOn (advance counter bookmark selected) c) d
        (advanceTime counter bookmark row) ∧
      d.workHead = WorkLanes.address counter base 0 ∧
      d.work = advanceWork bookmark selected base row c.work ∧
      WorkLanes.OriginTrack lanes base d.work ∧
      (∀ p, d.work (WorkLanes.address bookmark base p) = decide (p = row+3)) ∧
      SameIO c d := by
  let bound := base+(lanes+1)*(row+4)
  let F := advanceFootprint lanes base row
  let A1 := toBookmark counter bookmark
  let A2 := findBookmark lanes
  let A3 := clearBookmark
  let A4 := columnStart bookmark
  let A5 := BankColumnInitialize.machine lanes selected
  let A6 := markNext bookmark
  let A7 := originStart bookmark
  let A8 := originHome lanes
  let A9 := counterFlag counter
  have rowBound (lane : Fin lanes) (p : ℕ) (hp : p < row+4) :
      WorkLanes.address lane base p < bound := WorkLanes.address_lt_prefix lane base _ _ hp
  have markerBound (p : ℕ) (hp : p < row+4) :
      WorkLanes.markerAddress lanes base p < bound := WorkLanes.marker_lt_prefix lanes base _ _ hp
  have inRange (lane : Fin lanes) (p : ℕ) (hl : row ≤ p) (hr : p < row+4) :
      WorkLanes.address lane base p ∈ F.work := by
    have hs := Nat.mul_le_mul_left (lanes+1) hl
    exact ⟨by dsimp [WorkLanes.address]; omega, rowBound lane p hr⟩
  have colend : base+(lanes+1)*row+BankColumnInitialize.steps lanes =
      base+(lanes+1)*(row+3) := by dsimp [BankColumnInitialize.steps]; ring
  have endBound : base+(lanes+1)*(row+3) < bound := by
    have H := markerBound (row+3) (by omega)
    dsimp [WorkLanes.markerAddress] at H
    omega
  obtain ⟨d1,H1,h1h,h1w,h1IO⟩ := NativeMSBFold.moveFlag_exec counter bookmark input c base hi hc
    (by simpa only [WorkLanes.address,Nat.mul_zero,Nat.add_zero] using hhead)
  have H1f : FirstExit (A1.step input) (fun _ e => e.workHead < bound ∧ Frame F c e)
      {e | e.state=none} (startOn A1 c) d1 (NativeLaneFlagCopy.distance counter bookmark+1) :=
    firstExit_mono input c _ _ _ _ _ _ _ H1
      (by have H := markerBound 0 (by omega); dsimp [WorkLanes.markerAddress] at H; omega)
      (by simp) (by simp)
  have io1 : SameIO c d1 := h1IO
  have hi1 : d1.inputHead ≤ input.length+1 := by rw [io1.1]; exact hi
  have hc1 : d1.catalystHead ≤ d1.catalyst.length := by rw [io1.2.1,io1.2.2.1]; exact hc
  have hp2 (p : ℕ) : NativeLiteral.position .right d1.workHead (p*(lanes+1)) =
      WorkLanes.address bookmark base p := by
    rw [NativeLiteral.position_right,h1h]
    dsimp [WorkLanes.address]
    ring
  obtain ⟨d2,H2,h2h,h2w,h2IO⟩ := NativeMarkerSeek.seek_exec .right lanes input d1 row
    (WorkLanes.address bookmark base row) bound hi1 hc1 (hp2 row)
    (by rw [h1h]; simpa [WorkLanes.address] using rowBound bookmark 0 (by omega))
    (rowBound bookmark row (by omega))
    (by intro p hp; rw [hp2 p,h1w,unique]; simp [show p ≠ row by omega])
    (by rw [h1w,unique]; simp)
  have H2f := firstExit_mono input d1 _ _ _ _ _ _ F H2 le_rfl (by simp) (by simp)
  have io2 := sameIO_trans io1 h2IO
  have hi2 : d2.inputHead ≤ input.length+1 := by rw [io2.1]; exact hi
  have hc2 : d2.catalystHead ≤ d2.catalyst.length := by rw [io2.2.1,io2.2.2.1]; exact hc
  obtain ⟨d3,H3,h3h,h3w,h3IO⟩ := NativeLiteral.write_exec .stay 0 false input d2
    (WorkLanes.address bookmark base row) bound hi2 hc2
    (by simpa only [NativeLiteral.position] using h2h)
    (by rw [h2h]; exact rowBound bookmark row (by omega))
    (rowBound bookmark row (by omega))
  have H3f := firstExit_mono input d2 _ _ _ _ _ _ F H3 le_rfl
    (by intro p hp; simpa only [Set.mem_singleton_iff.mp hp] using inRange bookmark row le_rfl (by omega))
    (by simp)
  have io3 := sameIO_trans io2 h3IO
  have hi3 : d3.inputHead ≤ input.length+1 := by rw [io3.1]; exact hi
  have hc3 : d3.catalystHead ≤ d3.catalyst.length := by rw [io3.2.1,io3.2.2.1]; exact hc
  obtain ⟨d4,H4,h4h,h4w,h4IO⟩ := NativeLaneWordTransfer.move_exec .left bookmark.val input d3
    (base+(lanes+1)*row) bound hi3 hc3
    (by rw [NativeLiteral.position_left,h3h]; dsimp [WorkLanes.address]; omega)
    (by rw [h3h]; exact rowBound bookmark row (by omega))
    (by have H := markerBound row (by omega); dsimp [WorkLanes.markerAddress] at H; omega)
  have H4f := firstExit_mono input d3 _ _ _ _ _ _ F H4 le_rfl (by simp) (by simp)
  have io4 := sameIO_trans io3 h4IO
  have hi4 : d4.inputHead ≤ input.length+1 := by rw [io4.1]; exact hi
  have hc4 : d4.catalystHead ≤ d4.catalyst.length := by rw [io4.2.1,io4.2.2.1]; exact hc
  obtain ⟨d5,H5,h5h,h5w,h5IO⟩ := BankColumnInitialize.column_exec lanes selected input d4 bound hi4 hc4
    (by rw [h4h,colend]; exact endBound)
  have H5f := firstExit_mono input d4 _ _ _ _ _ _ F H5 le_rfl
    (by
      intro p hp
      change d4.workHead ≤ p ∧ p < d4.workHead+BankColumnInitialize.steps lanes ∧ _ at hp
      rw [h4h,colend] at hp
      exact ⟨hp.1,lt_trans hp.2.1 endBound⟩)
    (by exact Set.Subset.refl _)
  have io5 := sameIO_trans io4 h5IO
  have hi5 : d5.inputHead ≤ input.length+1 := by rw [io5.1]; exact hi
  have hc5 : d5.catalystHead ≤ d5.catalyst.length := by rw [io5.2.1,io5.2.2.1]; exact hc
  have h5head : d5.workHead=base+(lanes+1)*(row+3) := by rw [h5h,h4h,colend]
  obtain ⟨d6,H6,h6h,h6w,h6IO⟩ := NativeLiteral.write_exec .right bookmark.val true input d5
    (WorkLanes.address bookmark base (row+3)) bound hi5 hc5
    (by rw [NativeLiteral.position_right,h5head]; rfl)
    (by rw [h5head]; exact endBound)
    (rowBound bookmark (row+3) (by omega))
  have H6f := firstExit_mono input d5 _ _ _ _ _ _ F H6 le_rfl
    (by intro p hp; simpa only [Set.mem_singleton_iff.mp hp] using inRange bookmark (row+3) (by omega) (by omega))
    (by simp)
  have io6 := sameIO_trans io5 h6IO
  have hi6 : d6.inputHead ≤ input.length+1 := by rw [io6.1]; exact hi
  have hc6 : d6.catalystHead ≤ d6.catalyst.length := by rw [io6.2.1,io6.2.2.1]; exact hc
  have h6work : d6.work=advanceWork bookmark selected base row c.work := by
    rw [h6w,h5w,h4h,h4w,h3w,h2w,h1w]
    rfl
  obtain ⟨d7,H7,h7h,h7w,h7IO⟩ := NativeLaneWordTransfer.move_exec .right (lanes-bookmark.val) input d6
    (WorkLanes.markerAddress lanes base (row+3)) bound hi6 hc6
    (by rw [NativeLiteral.position_right,h6h]; dsimp [WorkLanes.address,WorkLanes.markerAddress]; omega)
    (by rw [h6h]; exact rowBound bookmark (row+3) (by omega))
    (markerBound (row+3) (by omega))
  have H7f := firstExit_mono input d6 _ _ _ _ _ _ F H7 le_rfl (by simp) (by simp)
  have io7 := sameIO_trans io6 h7IO
  have hi7 : d7.inputHead ≤ input.length+1 := by rw [io7.1]; exact hi
  have hc7 : d7.catalystHead ≤ d7.catalyst.length := by rw [io7.2.1,io7.2.2.1]; exact hc
  have origin7 : WorkLanes.OriginTrack lanes base d7.work := by
    rw [h7w,h6work]
    exact advance_origin bookmark selected base row c.work origin
  have hp8 (p : ℕ) (hp : p ≤ row+3) :
      NativeLiteral.position .left d7.workHead (p*(lanes+1)) =
        WorkLanes.markerAddress lanes base (row+3-p) := by
    rw [NativeLiteral.position_left,h7h]
    have hs := Nat.mul_le_mul_right (lanes+1) hp
    have he : (row+3-p)*(lanes+1)=(row+3)*(lanes+1)-p*(lanes+1) := Nat.sub_mul _ _ _
    dsimp [WorkLanes.markerAddress]
    rw [Nat.mul_comm (lanes+1) (row+3-p),he,
      Nat.mul_comm (lanes+1) (row+3)]
    omega
  have hp8end : NativeLiteral.position .left d7.workHead ((row+3)*(lanes+1)) =
      WorkLanes.markerAddress lanes base 0 := by simpa only [Nat.sub_self] using hp8 (row+3) le_rfl
  obtain ⟨d8,H8,h8h,h8w,h8IO⟩ := NativeMarkerSeek.seek_exec .left lanes input d7 (row+3)
    (WorkLanes.markerAddress lanes base 0) bound hi7 hc7 hp8end
    (by rw [h7h]; exact markerBound (row+3) (by omega)) (markerBound 0 (by omega))
    (by intro p hp; rw [hp8 p (by omega),origin7]; simp [show row+3-p ≠ 0 by omega])
    (by simpa using origin7 0)
  have H8f := firstExit_mono input d7 _ _ _ _ _ _ F H8 le_rfl (by simp) (by simp)
  have io8 := sameIO_trans io7 h8IO
  have hi8 : d8.inputHead ≤ input.length+1 := by rw [io8.1]; exact hi
  have hc8 : d8.catalystHead ≤ d8.catalyst.length := by rw [io8.2.1,io8.2.2.1]; exact hc
  obtain ⟨d9,H9,h9h,h9w,h9IO⟩ := NativeLaneWordTransfer.move_exec .left (lanes-counter.val) input d8
    (WorkLanes.address counter base 0) bound hi8 hc8
    (by rw [NativeLiteral.position_left,h8h]; dsimp [WorkLanes.address,WorkLanes.markerAddress]; omega)
    (by rw [h8h]; exact markerBound 0 (by omega)) (rowBound counter 0 (by omega))
  have H9f := firstExit_mono input d8 _ _ _ _ _ _ F H9 le_rfl (by simp) (by simp)
  have io9 := sameIO_trans io8 h9IO
  let t1 := NativeLaneFlagCopy.distance counter bookmark+1
  let t2 := row*(lanes+1)+1
  let t3 := 1
  let t4 := bookmark.val+1
  let t5 := BankColumnInitialize.steps lanes
  let t6 := bookmark.val+1
  let t7 := lanes-bookmark.val+1
  let t8 := (row+3)*(lanes+1)+1
  let t9 := lanes-counter.val+1
  have chain8 := framed_seq A8 (A9) input d7 d8 (d9) t8 (t9) bound F H8f H9f
  let e8 := Sequential.rightConfig A8 (A9) (d9)
  have chain7 := framed_seq A7 (Sequential.machine A8 (A9)) input d6 d7 (e8) t7 (t8+(t9)) bound F H7f chain8
  let e7 := Sequential.rightConfig A7 (Sequential.machine A8 (A9)) (e8)
  have chain6 := framed_seq A6 (Sequential.machine A7 (Sequential.machine A8 (A9))) input d5 d6 (e7) t6 (t7+(t8+(t9))) bound F H6f chain7
  let e6 := Sequential.rightConfig A6 (Sequential.machine A7 (Sequential.machine A8 (A9))) (e7)
  have chain5 := framed_seq A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9)))) input d4 d5 (e6) t5 (t6+(t7+(t8+(t9)))) bound F H5f chain6
  let e5 := Sequential.rightConfig A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9)))) (e6)
  have chain4 := framed_seq A4 (Sequential.machine A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9))))) input d3 d4 (e5) t4 (t5+(t6+(t7+(t8+(t9))))) bound F H4f chain5
  let e4 := Sequential.rightConfig A4 (Sequential.machine A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9))))) (e5)
  have chain3 := framed_seq A3 (Sequential.machine A4 (Sequential.machine A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9)))))) input d2 d3 (e4) t3 (t4+(t5+(t6+(t7+(t8+(t9)))))) bound F H3f chain4
  let e3 := Sequential.rightConfig A3 (Sequential.machine A4 (Sequential.machine A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9)))))) (e4)
  have chain2 := framed_seq A2 (Sequential.machine A3 (Sequential.machine A4 (Sequential.machine A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9))))))) input d1 d2 (e3) t2 (t3+(t4+(t5+(t6+(t7+(t8+(t9))))))) bound F H2f chain3
  let e2 := Sequential.rightConfig A2 (Sequential.machine A3 (Sequential.machine A4 (Sequential.machine A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9))))))) (e3)
  have chain1 := framed_seq A1 (Sequential.machine A2 (Sequential.machine A3 (Sequential.machine A4 (Sequential.machine A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9)))))))) input c d1 (e2) t1 (t2+(t3+(t4+(t5+(t6+(t7+(t8+(t9)))))))) bound F H1f chain2
  let e1 := Sequential.rightConfig A1 (Sequential.machine A2 (Sequential.machine A3 (Sequential.machine A4 (Sequential.machine A5 (Sequential.machine A6 (Sequential.machine A7 (Sequential.machine A8 (A9)))))))) (e2)
  have hwork : e1.work=advanceWork bookmark selected base row c.work := by
    change d9.work=_
    rw [h9w,h8w,h7w,h6work]
  refine ⟨e1,?_,h9h,hwork,?_,?_,io9⟩
  · exact chain1
  · rw [hwork]
    exact advance_origin bookmark selected base row c.work origin
  · intro p
    rw [hwork]
    exact advance_bookmark bookmark selected notSelected base row c.work unique p

end CatalyticTreeEval.Contracts.NativeBankAllocate
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeMSBFoldPorts -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeMSBFold

open NativeRoundSupport

/-- The source routine's logical work view at a lane's ABI flag zero. All
read-only input, output, and catalyst fields are the actual caller fields. -/
def logicalStart {N : Main.Machine} {lanes : ℕ} (A : Main.Machine)
    (lane : Fin lanes) (base : ℕ) (c : Config N) : Config A :=
  { c with
    state := some A.start
    workHead := 0
    work := fun p => c.work (WorkLanes.address lane base p) }

theorem logicalStart_matches {N : Main.Machine} {lanes : ℕ} (A : Main.Machine)
    (lane : Fin lanes) (base : ℕ) (c : Config N) :
    WorkLanes.Matches lane base (logicalStart A lane base c).work c.work := fun _ => rfl

theorem embed_logicalStart {N : Main.Machine} {lanes : ℕ} (A : Main.Machine)
    (lane : Fin lanes) (base : ℕ) (c : Config N) (hhead : c.workHead = base + lane.val) :
    WorkLanes.embed A lanes lane base (logicalStart A lane base c) c.work =
      startOn (WorkLanes.machine A lanes lane) c := by
  cases c
  simp_all [logicalStart, WorkLanes.embed, WorkLanes.snapshot, WorkLanes.address,
    WorkLanes.machine, startOn]

theorem logicalStart_flag {N : Main.Machine} {lanes : ℕ} (A : Main.Machine)
    (lane : Fin lanes) (base : ℕ) (c : Config N) :
    (logicalStart A lane base c).work 0 = c.work (base + lane.val) := by
  simp [logicalStart, WorkLanes.address]

end CatalyticTreeEval.Contracts.NativeMSBFold
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneShuttle -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

@[simp] theorem remaining_zero {lanes : ℕ} (r : Fin (lanes + 1)) : remaining r 0 = r := by
  apply Fin.ext
  simp [remaining]

theorem remaining_succ {lanes : ℕ} (r : Fin (lanes + 1)) (u : ℕ) :
    predecessor (remaining r u) = remaining r (u + 1) := by
  apply Fin.ext
  dsimp [remaining, predecessor]
  omega

theorem run_outward (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (r : Fin (lanes + 1)) (head : ℕ)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length) :
    ∀ u ≤ r.val, runFrom ((machine A lanes lane).step input)
      (snapshot A lanes lane source physical (some (outward A lanes q r)) head) u =
      some (snapshot A lanes lane source physical
        (some (outward A lanes q (remaining r u))) (head + u)) := by
  intro u
  induction u with
  | zero => intro _; simp only [runFrom_zero, remaining_zero, Nat.add_zero]
  | succ u ih =>
      intro hu
      rw [runFrom_succ, ih (by omega)]
      have H := step_outward A lanes lane input source physical q (remaining r u) (head + u)
        (by dsimp [remaining]; omega) hi hc
      simpa only [Option.bind_some, remaining_succ, Nat.add_assoc] using H

theorem run_inward (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (origin : Bool) (r : Fin (lanes + 1)) (head : ℕ)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length) :
    ∀ u ≤ r.val, runFrom ((machine A lanes lane).step input)
      (snapshot A lanes lane source physical (some (inward A lanes q origin r)) head) u =
      some (snapshot A lanes lane source physical
        (some (inward A lanes q origin (remaining r u))) (head - u)) := by
  intro u
  induction u with
  | zero => intro _; simp only [runFrom_zero, remaining_zero, Nat.sub_zero]
  | succ u ih =>
      intro hu
      rw [runFrom_succ, ih (by omega)]
      have H := step_inward A lanes lane input source physical q origin (remaining r u) (head - u)
        (by dsimp [remaining]; omega) hi hc
      simpa only [Option.bind_some, remaining_succ, Nat.sub_sub] using H

/-- Fetch the immutable origin marker and return to the source cell. Every
physical work bit, input/catalyst head and output bit is preserved. -/
theorem run_shuttle (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (head : ℕ)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length) :
    runFrom ((machine A lanes lane).step input)
      (snapshot A lanes lane source physical (some (outward A lanes q (counter lane))) head)
      (2 * distance lane) =
      some (snapshot A lanes lane source physical
        (some (inward A lanes q (physical (head + distance lane)) ⟨0, by omega⟩)) head) := by
  have positive := distance_pos lane
  have out := run_outward A lanes lane input source physical q (counter lane) head hi hc
    (distance lane) le_rfl
  have back := run_inward A lanes lane input source physical q
    (physical (head + distance lane)) (predecessor (counter lane))
    (head + distance lane - 1) hi hc (distance lane - 1) le_rfl
  have head_back : head + distance lane - 1 - (distance lane - 1) = head := by omega
  have end_counter : remaining (predecessor (counter lane)) (distance lane - 1) =
      (⟨0, by omega⟩ : Fin (lanes + 1)) := by
    apply Fin.ext
    simp [remaining, predecessor, counter]
  have out_counter : remaining (counter lane) (distance lane) =
      (⟨0, by omega⟩ : Fin (lanes + 1)) := by
    apply Fin.ext
    simp [remaining, counter]
  rw [out_counter] at out
  rw [show 2 * distance lane = distance lane + (1 + (distance lane - 1)) by omega,
    runFrom_add, out]
  simp only [Option.bind_some]
  rw [runFrom_add]
  simp only [runFrom_succ, runFrom_zero, Option.bind_some]
  rw [step_marker A lanes lane input source physical q (head + distance lane) hi hc]
  simpa only [Option.bind_some, end_counter, head_back] using back

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLanePending -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

theorem drift_zero (direction : Option Bool) (head : ℕ) : drift direction head 0 = head := by
  cases direction with
  | none => rfl
  | some b => cases b <;> simp [drift]

theorem drift_succ (direction : Option Bool) (head u : ℕ) :
    (decodeMove direction).apply (drift direction head u) = drift direction head (u + 1) := by
  cases direction with
  | none => rfl
  | some b => cases b <;> simp [drift, decodeMove, Move.apply, Nat.sub_sub, Nat.add_assoc]

theorem step_pending (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (next : Option (Fin A.states)) (direction : Option Bool) (r : Fin (lanes + 1)) (head : ℕ)
    (positive : 0 < r.val)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length) :
    (machine A lanes lane).step input
      (snapshot A lanes lane source physical (some (pending A lanes next direction r)) head) =
      some (snapshot A lanes lane source physical (pendingNext A lanes lane next direction r)
        ((decodeMove direction).apply head)) := by
  simp [Machine.step, snapshot, machine, instruction, pending, quietInstruction,
    positive.ne', Move.apply, hi, hc, Function.update_eq_self]

theorem run_pending_prefix (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (next : Option (Fin A.states)) (direction : Option Bool) (r : Fin (lanes + 1)) (head : ℕ)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length) :
    ∀ u < r.val, runFrom ((machine A lanes lane).step input)
      (snapshot A lanes lane source physical (some (pending A lanes next direction r)) head) u =
      some (snapshot A lanes lane source physical
        (some (pending A lanes next direction (remaining r u))) (drift direction head u)) := by
  intro u
  induction u with
  | zero => intro _; simp only [runFrom_zero, remaining_zero, drift_zero]
  | succ u ih =>
      intro hu
      rw [runFrom_succ, ih (by omega)]
      have positive : 0 < (remaining r u).val := by dsimp [remaining]; omega
      have more : ¬ (remaining r u).val ≤ 1 := by dsimp [remaining]; omega
      have H := step_pending A lanes lane input source physical next direction (remaining r u)
        (drift direction head u) positive hi hc
      simpa only [Option.bind_some, pendingNext, if_neg more, remaining_succ, drift_succ] using H

theorem run_pending (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (next : Option (Fin A.states)) (direction : Option Bool) (r : Fin (lanes + 1)) (head : ℕ)
    (positive : 0 < r.val)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length) :
    runFrom ((machine A lanes lane).step input)
      (snapshot A lanes lane source physical (some (pending A lanes next direction r)) head) r.val =
      some (snapshot A lanes lane source physical (resumed A lanes lane next)
        (drift direction head r.val)) := by
  have H := run_pending_prefix A lanes lane input source physical next direction r head hi hc
    (r.val - 1) (by omega)
  have last : (remaining r (r.val - 1)).val = 1 := by dsimp [remaining]; omega
  rw [show r.val = r.val - 1 + 1 by omega, runFrom_succ, H]
  have S := step_pending A lanes lane input source physical next direction (remaining r (r.val - 1))
    (drift direction head (r.val - 1)) (by omega) hi hc
  simpa only [Option.bind_some, pendingNext, last, le_rfl, if_true, drift_succ,
    show r.val - 1 + 1 = r.val by omega] using S

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneApply -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

theorem origin_eq_beq (p : ℕ) : decide (p = 0) = (p == 0) := by
  cases p <;> rfl

theorem source_step_spec (A : Machine) (input : List Bool) (c d : Configuration A)
    (q : Fin A.states) (state : c.state = some q) :
    A.step input c = some d ↔
      Legal A input c (sourceInstruction A input c q) ∧
        d = sourceResult A c (sourceInstruction A input c q) := by
  simp only [Machine.step, state]
  change (if Legal A input c (sourceInstruction A input c q) then
    some (sourceResult A c (sourceInstruction A input c q)) else none) = some d ↔ _
  by_cases legal : Legal A input c (sourceInstruction A input c q)
  · simp [legal, eq_comm]
  · simp [legal]

/-- The only tape-changing instruction in a simulation macro is the actual
source instruction. Input/catalyst actions and output occur exactly once. -/
theorem step_apply (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state = some q)
    (workMatches : Matches lane base source.work physical)
    (step : A.step input source = some target) :
    let a := sourceInstruction A input source q
    let direction := moveCode (clippedMove (decide (source.workHead = 0)) a.workMove)
    let updated := Function.update physical (address lane base source.workHead) a.workWrite
    (machine A lanes lane).step input
      (snapshot A lanes lane source physical
        (some (inward A lanes q (decide (source.workHead = 0)) ⟨0, by omega⟩))
        (address lane base source.workHead)) =
      some (snapshot A lanes lane target updated
        (some (pending A lanes target.state direction ⟨lanes, by omega⟩))
        ((clippedMove (decide (source.workHead = 0)) a.workMove).apply
          (address lane base source.workHead))) := by
  dsimp only
  obtain ⟨legal, target_eq⟩ := (source_step_spec A input source target q state).mp step
  subst target
  let a := sourceInstruction A input source q
  have instruction_eq :
      (machine A lanes lane).table
        (encode A lanes (inward A lanes q (decide (source.workHead = 0)) ⟨0, by omega⟩))
        (if source.inputHead = 0 then none else input[source.inputHead - 1]?)
        (physical (address lane base source.workHead)) source.catalyst[source.catalystHead]?
        (source.inputHead == 0) (address lane base source.workHead == 0)
        (source.catalystHead == 0) =
      applyInstruction A lanes a (decide (source.workHead = 0)) := by
    simp only [machine, Equiv.symm_apply_apply, instruction, inward, Fin.val_zero, if_true]
    rw [workMatches source.workHead]
    simp only [origin_eq_beq]
    rfl
  simp only [Machine.step, snapshot, Option.map_some]
  rw [instruction_eq]
  change (if Legal A input source a then some _ else none) = _
  rw [if_pos legal]
  rfl

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeRunLaws -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts

open CatalyticMatching.General

theorem step_catalyst_length (M : Machine) (input : List Bool) {c d : Configuration M}
    (step : M.step input c = some d) : d.catalyst.length = c.catalyst.length := by
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases state with
    | none =>
        simp only [Machine.step] at step
        cases step
        rfl
    | some q =>
        let a := M.table q (if ih = 0 then none else input[ih - 1]?)
          (work wh) catalyst[ch]? (ih == 0) (wh == 0) (ch == 0)
        change (if a.inputMove.apply ih ≤ input.length + 1 ∧
          a.catalystMove.apply ch ≤ catalyst.length ∧
          (a.catalystWrite.isSome → ch < catalyst.length) then some _ else none) = some d
          at step
        by_cases guard : a.inputMove.apply ih ≤ input.length + 1 ∧
          a.catalystMove.apply ch ≤ catalyst.length ∧
          (a.catalystWrite.isSome → ch < catalyst.length)
        · rw [if_pos guard] at step
          cases step
          cases write : a.catalystWrite <;> simp [a, write]
        · rw [if_neg guard] at step
          contradiction

theorem runFrom_catalyst_length (M : Machine) (input : List Bool)
    {c d : Configuration M} {t : ℕ} (result : runFrom (M.step input) c t = some d) :
    d.catalyst.length = c.catalyst.length := by
  induction t generalizing d with
  | zero =>
      have heq : c = d := by simpa only [runFrom_zero, Option.some.injEq] using result
      exact congrArg (fun e : Configuration M => e.catalyst.length) heq.symm
  | succ t ih =>
      cases hr : runFrom (M.step input) c t with
      | none => simp [runFrom_succ, hr] at result
      | some e =>
          have last : M.step input e = some d := by
            simpa only [runFrom_succ, hr, Option.bind_some] using result
          exact (step_catalyst_length M input last).trans (ih hr)

theorem run_catalyst_length (M : Machine) (input tape : List Bool)
    {d : Configuration M} {t : ℕ} (result : M.run input tape t = some d) :
    d.catalyst.length = tape.length := by
  have H : runFrom (M.step input) (M.initial tape) t = some d := by
    simpa only [runFrom_initial] using result
  exact runFrom_catalyst_length M input H

theorem step_headBounds (M : Machine) (input : List Bool) {c d : Configuration M}
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (step : M.step input c = some d) :
    d.inputHead ≤ input.length + 1 ∧ d.catalystHead ≤ d.catalyst.length := by
  have length := step_catalyst_length M input step
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases state with
    | none =>
        simp only [Machine.step] at step
        cases step
        exact ⟨hi, hc⟩
    | some q =>
        simp only [Machine.step] at step
        split_ifs at step <;> cases step <;> simp_all

theorem run_headBounds (M : Machine) (input tape : List Bool)
    {d : Configuration M} {t : ℕ} (result : M.run input tape t = some d) :
    d.inputHead ≤ input.length + 1 ∧ d.catalystHead ≤ d.catalyst.length := by
  induction t generalizing d with
  | zero =>
      simp only [Machine.run, Option.some.injEq] at result
      subst d
      simp [Machine.initial]
  | succ t ih =>
      cases hr : M.run input tape t with
      | none => simp [Machine.run, hr] at result
      | some e =>
          have last : M.step input e = some d := by
            simpa only [Machine.run, hr, Option.bind_some] using result
          exact step_headBounds M input (ih hr).1 (ih hr).2 last

theorem step_work_away (M : Machine) (input : List Bool) {c d : Configuration M}
    (step : M.step input c = some d) (p : ℕ) (away : p ≠ c.workHead) : d.work p = c.work p := by
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases state with
    | none =>
        simp only [Machine.step] at step
        cases step
        rfl
    | some q =>
        simp only [Machine.step] at step
        split_ifs at step <;> cases step <;> simp_all

theorem run_work_zero_above (M : Machine) (input tape : List Bool) {T bound : ℕ}
    (workBound : M.workBound input tape T bound) :
    ∀ u ≤ T, ∀ d, M.run input tape u = some d → ∀ p, bound ≤ p → d.work p = false := by
  intro u
  induction u with
  | zero =>
      intro _ d hd p _
      simp only [Machine.run, Option.some.injEq] at hd
      subst d
      rfl
  | succ u ih =>
      intro hu d hd p hp
      cases hr : M.run input tape u with
      | none => simp [Machine.run, hr] at hd
      | some e =>
          have last : M.step input e = some d := by
            simpa only [Machine.run, hr, Option.bind_some] using hd
          have head := workBound u (by omega) e hr
          rw [step_work_away M input last p (by omega)]
          exact ih (by omega) e hr p hp

theorem runFrom_halted (M : Machine) (input : List Bool) (c : Configuration M)
    (halt : c.state = none) (t : ℕ) : runFrom (M.step input) c t = some c := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [runFrom_succ, ih, Option.bind_some, Machine.step, halt]

end CatalyticTreeEval.Contracts
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneMacro -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

/-- One successful live source step is implemented by a constant number of
actual finite binary transitions, including the origin lookup and move padding. -/
theorem run_macro (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state = some q)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : OriginTrack lanes base physical)
    (workMatches : Matches lane base source.work physical)
    (step : A.step input source = some target) :
    let a := sourceInstruction A input source q
    let updated := Function.update physical (address lane base source.workHead) a.workWrite
    runFrom ((machine A lanes lane).step input)
      (embed A lanes lane base source physical) (macroTime lane) =
      some (embed A lanes lane base target updated) := by
  dsimp only
  let a := sourceInstruction A input source q
  let updated := Function.update physical (address lane base source.workHead) a.workWrite
  let direction := moveCode (clippedMove (decide (source.workHead = 0)) a.workMove)
  let firstHead := (clippedMove (decide (source.workHead = 0)) a.workMove).apply
    (address lane base source.workHead)
  have marker : physical (address lane base source.workHead + distance lane) =
      decide (source.workHead = 0) := by
    rw [address_add_distance]
    exact origin source.workHead
  have fetch := run_shuttle A lanes lane input source physical q
    (address lane base source.workHead) hi hc
  rw [marker] at fetch
  have fetch' : runFrom ((machine A lanes lane).step input)
      (embed A lanes lane base source physical) (2 * distance lane) =
      some (snapshot A lanes lane source physical
        (some (inward A lanes q (decide (source.workHead = 0)) ⟨0, by omega⟩))
        (address lane base source.workHead)) := by
    simpa only [embed, state, Option.map_some] using fetch
  have applyStep := step_apply A lanes lane base input source target physical q state workMatches step
  have targetBounds := step_headBounds A input hi hc step
  have targetEq := ((source_step_spec A input source target q state).mp step).2
  have targetHead : target.workHead = a.workMove.apply source.workHead :=
    congrArg (fun c : Configuration A => c.workHead) targetEq
  have finalHead : drift direction firstHead lanes = address lane base target.workHead := by
    rw [targetHead]
    exact padded_work_move lane base source.workHead a.workMove
  have lanesPositive : 0 < lanes := Nat.lt_of_le_of_lt (Nat.zero_le lane.val) lane.isLt
  have padded := run_pending A lanes lane input target updated target.state direction
    (⟨lanes, Nat.lt_succ_self lanes⟩ : Fin (lanes + 1)) firstHead lanesPositive
    targetBounds.1 targetBounds.2
  have finish : runFrom ((machine A lanes lane).step input)
      (snapshot A lanes lane target updated
        (some (pending A lanes target.state direction ⟨lanes, by omega⟩)) firstHead) lanes =
      some (embed A lanes lane base target updated) := by
    simpa only [embed, resumed, finalHead] using padded
  rw [show macroTime lane = 2 * distance lane + (1 + lanes) by dsimp [macroTime]; omega,
    runFrom_add, fetch']
  simp only [Option.bind_some]
  rw [runFrom_add]
  simp only [runFrom_succ, runFrom_zero, Option.bind_some]
  rw [applyStep]
  exact finish

theorem macro_preserves_lanes (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state = some q)
    (origin : OriginTrack lanes base physical)
    (workMatches : Matches lane base source.work physical)
    (step : A.step input source = some target) :
    let a := sourceInstruction A input source q
    let updated := Function.update physical (address lane base source.workHead) a.workWrite
    OriginTrack lanes base updated ∧ Matches lane base target.work updated ∧
      (∀ other : Fin lanes, other ≠ lane → ∀ p,
        updated (address other base p) = physical (address other base p)) := by
  dsimp only
  have targetEq := ((source_step_spec A input source target q state).mp step).2
  refine ⟨update_origin lane base physical origin source.workHead _, ?_, ?_⟩
  · rw [targetEq]
    exact update_matches lane base source.work physical workMatches source.workHead _
  · intro other different p
    exact update_other_lane lane other base physical different source.workHead p _

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneFailure -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

theorem step_apply_failed (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state = some q)
    (workMatches : Matches lane base source.work physical)
    (failed : A.step input source = none) :
    (machine A lanes lane).step input
      (snapshot A lanes lane source physical
        (some (inward A lanes q (decide (source.workHead = 0)) ⟨0, by omega⟩))
        (address lane base source.workHead)) = none := by
  let a := sourceInstruction A input source q
  have illegal : ¬ Legal A input source a := by
    intro legal
    have success := (source_step_spec A input source (sourceResult A source a) q state).mpr
      ⟨legal, rfl⟩
    rw [failed] at success
    contradiction
  have instruction_eq :
      (machine A lanes lane).table
        (encode A lanes (inward A lanes q (decide (source.workHead = 0)) ⟨0, by omega⟩))
        (if source.inputHead = 0 then none else input[source.inputHead - 1]?)
        (physical (address lane base source.workHead)) source.catalyst[source.catalystHead]?
        (source.inputHead == 0) (address lane base source.workHead == 0)
        (source.catalystHead == 0) =
      applyInstruction A lanes a (decide (source.workHead = 0)) := by
    simp only [machine, Equiv.symm_apply_apply, instruction, inward, if_true]
    rw [workMatches source.workHead]
    simp only [origin_eq_beq]
    rfl
  simp only [Machine.step, snapshot, Option.map_some]
  rw [instruction_eq]
  change (if Legal A input source a then some _ else none) = none
  rw [if_neg illegal]

/-- Native failure is propagated through the finite origin-lookup host. -/
theorem run_macro_failed (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : OriginTrack lanes base physical)
    (workMatches : Matches lane base source.work physical)
    (failed : A.step input source = none) :
    runFrom ((machine A lanes lane).step input)
      (embed A lanes lane base source physical) (macroTime lane) = none := by
  cases state : source.state with
  | none => simp [Machine.step, state] at failed
  | some q =>
      have marker : physical (address lane base source.workHead + distance lane) =
          decide (source.workHead = 0) := by
        rw [address_add_distance]
        exact origin source.workHead
      have fetch := run_shuttle A lanes lane input source physical q
        (address lane base source.workHead) hi hc
      rw [marker] at fetch
      have fetch' : runFrom ((machine A lanes lane).step input)
          (embed A lanes lane base source physical) (2 * distance lane) =
          some (snapshot A lanes lane source physical
            (some (inward A lanes q (decide (source.workHead = 0)) ⟨0, by omega⟩))
            (address lane base source.workHead)) := by
        simpa only [embed, state, Option.map_some] using fetch
      rw [show macroTime lane = 2 * distance lane + (1 + lanes) by dsimp [macroTime]; omega,
        runFrom_add, fetch']
      simp only [Option.bind_some]
      rw [runFrom_add]
      simp only [runFrom_succ, runFrom_zero, Option.bind_some]
      rw [step_apply_failed A lanes lane base input source physical q state workMatches failed]
      rfl

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneRun -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

/-- Semantic bookkeeping only; this is not additional native control or memory. -/
structure ValidState (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ) (input : List Bool) where
  source : Configuration A
  physical : ℕ → Bool
  origin : OriginTrack lanes base physical
  workMatches : Matches lane base source.work physical
  inputBound : source.inputHead ≤ input.length + 1
  catalystBound : source.catalystHead ≤ source.catalyst.length

def afterWork (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ) (input : List Bool)
    (source : Configuration A) (physical : ℕ → Bool) : ℕ → Bool :=
  match source.state with
  | none => physical
  | some q => Function.update physical (address lane base source.workHead)
      (sourceInstruction A input source q).workWrite

noncomputable def nativeState {A : Machine} {lanes : ℕ} {lane : Fin lanes} {base : ℕ}
    {input : List Bool} (s : ValidState A lanes lane base input) : Configuration (machine A lanes lane) :=
  embed A lanes lane base s.source s.physical

theorem after_preserves (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (s : ValidState A lanes lane base input) (target : Configuration A)
    (step : A.step input s.source = some target) :
    OriginTrack lanes base (afterWork A lanes lane base input s.source s.physical) ∧
      Matches lane base target.work (afterWork A lanes lane base input s.source s.physical) := by
  cases state : s.source.state with
  | none =>
      have equal : s.source = target := by
        simpa only [Machine.step, state, Option.some.injEq] using step
      simpa only [afterWork, state, ← equal] using And.intro s.origin s.workMatches
  | some q =>
      have H := macro_preserves_lanes A lanes lane base input s.source target s.physical
        q state s.origin s.workMatches step
      simpa only [afterWork, state] using And.intro H.1 H.2.1

/-- One source step with its physically represented work state. -/
noncomputable def advance (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (s : ValidState A lanes lane base input) :
    Option (ValidState A lanes lane base input) :=
  match step : A.step input s.source with
  | none => none
  | some target =>
    some {
      source := target
      physical := afterWork A lanes lane base input s.source s.physical
      origin := (after_preserves A lanes lane base input s target step).1
      workMatches := (after_preserves A lanes lane base input s target step).2
      inputBound := (step_headBounds A input s.inputBound s.catalystBound step).1
      catalystBound := (step_headBounds A input s.inputBound s.catalystBound step).2 }

theorem advance_source (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (s : ValidState A lanes lane base input) :
    (advance A lanes lane base input s).map (fun t => t.source) = A.step input s.source := by
  unfold advance
  split <;> simp_all

theorem advance_native (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (s : ValidState A lanes lane base input) :
    runFrom ((machine A lanes lane).step input) (nativeState s) (macroTime lane) =
      (advance A lanes lane base input s).map nativeState := by
  unfold advance
  split
  · rename_i step
    simp only [Option.map_none]
    exact run_macro_failed A lanes lane base input s.source s.physical
      s.inputBound s.catalystBound s.origin s.workMatches step
  · rename_i target step
    simp only [Option.map_some]
    cases state : s.source.state with
    | none =>
        have equal : s.source = target := by
          simpa only [Machine.step, state, Option.some.injEq] using step
        subst target
        have halted : (nativeState s).state = none := by simp [nativeState, embed, snapshot, state]
        rw [runFrom_halted _ input _ halted]
        simp only [nativeState, afterWork, state]
    | some q =>
        have H := run_macro A lanes lane base input s.source target s.physical q state
          s.inputBound s.catalystBound s.origin s.workMatches step
        simpa only [nativeState, afterWork, state] using H

theorem grouped_run {C : Type} (step : C → Option C) (c : C) (width n : ℕ) :
    runFrom (fun d => runFrom step d width) c n = runFrom step c (n * width) := by
  induction n with
  | zero => simp only [Nat.zero_mul, runFrom_zero]
  | succ n ih => rw [runFrom_succ, ih, Nat.succ_mul, runFrom_add]

/-- Whole native trajectories agree at every source-step boundary. -/
theorem run_native (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (s : ValidState A lanes lane base input) (n : ℕ) :
    runFrom ((machine A lanes lane).step input) (nativeState s) (n * macroTime lane) =
      (runFrom (advance A lanes lane base input) s n).map nativeState := by
  rw [← grouped_run]
  exact runFrom_map (advance A lanes lane base input)
    (fun d => runFrom ((machine A lanes lane).step input) d (macroTime lane))
    nativeState (advance_native A lanes lane base input) s n

theorem run_source (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (s : ValidState A lanes lane base input) (n : ℕ) :
    runFrom (A.step input) s.source n =
      (runFrom (advance A lanes lane base input) s n).map (fun t => t.source) :=
  runFrom_map (advance A lanes lane base input) (A.step input) (fun t => t.source)
    (fun t => (advance_source A lanes lane base input t).symm) s n

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneTrace -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

/-- Fields other than control and the physical work head at a macro prefix. -/
def DataEq (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (source : Configuration A) (physical : ℕ → Bool)
    (e : Configuration (machine A lanes lane)) : Prop :=
  e.work=physical ∧ e.catalyst=source.catalyst ∧ e.inputHead=source.inputHead ∧
    e.catalystHead=source.catalystHead ∧ e.output=source.output

 theorem snapshot_data (A : Machine) (lanes : ℕ) (lane : Fin lanes)
    (source : Configuration A) (physical : ℕ → Bool) (control : Option (Control A lanes)) (head : ℕ) :
    DataEq A lanes lane source physical (snapshot A lanes lane source physical control head) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Every prefix of origin lookup remains between its source cell and marker,
with a live finite control and no change to any data field. -/
 theorem shuttle_prefix (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state=some q)
    (hi : source.inputHead ≤ input.length+1) (hc : source.catalystHead ≤ source.catalyst.length)
    (u : ℕ) (hu : u ≤ 2*distance lane) (e : Configuration (machine A lanes lane))
    (he : runFrom ((machine A lanes lane).step input) (embed A lanes lane base source physical) u=some e) :
    ∃ control head, e=snapshot A lanes lane source physical (some control) head ∧
      address lane base source.workHead ≤ head ∧
      head ≤ markerAddress lanes base source.workHead := by
  let head := address lane base source.workHead
  have positive := distance_pos lane
  have hstart : embed A lanes lane base source physical=
      snapshot A lanes lane source physical (some (outward A lanes q (counter lane))) head := by
    simp [embed, state, head]
  rw [hstart] at he
  by_cases hout : u ≤ distance lane
  · rw [run_outward A lanes lane input source physical q (counter lane) head hi hc u hout] at he
    cases Option.some.inj he
    refine ⟨_, _, rfl, by dsimp [head]; omega, ?_⟩
    exact shuttle_le_marker lane base source.workHead u hout
  · have hend : remaining (counter lane) (distance lane)=(⟨0, by omega⟩ : Fin (lanes+1)) := by
      apply Fin.ext
      simp [remaining, counter]
    have out := run_outward A lanes lane input source physical q (counter lane) head hi hc
      (distance lane) le_rfl
    rw [hend] at out
    let v := u-(distance lane+1)
    have hv : v ≤ distance lane-1 := by dsimp [v]; omega
    have ht : u=distance lane+(1+v) := by dsimp [v]; omega
    rw [ht, runFrom_add, out, Option.bind_some, runFrom_add] at he
    simp only [runFrom_succ, runFrom_zero, Option.bind_some] at he
    rw [step_marker A lanes lane input source physical q (head+distance lane) hi hc] at he
    simp only [Option.bind_some] at he
    rw [run_inward A lanes lane input source physical q (physical (head+distance lane))
      (predecessor (counter lane)) (head+distance lane-1) hi hc v hv] at he
    cases Option.some.inj he
    refine ⟨_, _, rfl, ?_, ?_⟩
    · dsimp [head]
      omega
    · rw [← address_add_distance lane base source.workHead]
      dsimp [head]
      omega

 theorem drift_after_apply (move : Move) (head u : ℕ) :
    drift (moveCode move) (move.apply head) u=drift (moveCode move) head (u+1) := by
  cases move <;> simp only [drift, moveCode, Move.apply] <;> omega

/-- Every padded movement point lies between the two logical cell addresses,
including a clamped logical left move at zero. -/
 theorem pending_between {lanes : ℕ} (lane : Fin lanes) (base p : ℕ) (move : Move)
    (u : ℕ) (hu : u ≤ lanes) :
    min (address lane base p) (address lane base (move.apply p)) ≤
      drift (moveCode (clippedMove (decide (p=0)) move))
        ((clippedMove (decide (p=0)) move).apply (address lane base p)) u ∧
      drift (moveCode (clippedMove (decide (p=0)) move))
        ((clippedMove (decide (p=0)) move).apply (address lane base p)) u ≤
          max (address lane base p) (address lane base (move.apply p)) := by
  have H := drift_between (moveCode (clippedMove (decide (p=0)) move))
    (address lane base p) (lanes+1) (u+1) (by omega)
  have hend : drift (moveCode (clippedMove (decide (p=0)) move))
      (address lane base p) (lanes+1)=address lane base (move.apply p) := by
    rw [← drift_after_apply]
    exact padded_work_move lane base p move
  rw [hend, ← drift_after_apply] at H
  exact H

/-- Reachability of the live padded-move prefix after the unique data step. -/
 theorem pending_prefix_global (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state=some q)
    (hi : source.inputHead ≤ input.length+1) (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : OriginTrack lanes base physical) (workMatches : Matches lane base source.work physical)
    (step : A.step input source=some target) (u : ℕ) (hu : u < lanes) :
    let a := sourceInstruction A input source q
    let updated := Function.update physical (address lane base source.workHead) a.workWrite
    let direction := moveCode (clippedMove (decide (source.workHead=0)) a.workMove)
    let firstHead := (clippedMove (decide (source.workHead=0)) a.workMove).apply
      (address lane base source.workHead)
    runFrom ((machine A lanes lane).step input) (embed A lanes lane base source physical)
      (2*distance lane+1+u)=
      some (snapshot A lanes lane target updated
        (some (pending A lanes target.state direction (remaining ⟨lanes, by omega⟩ u)))
        (drift direction firstHead u)) := by
  dsimp only
  have marker : physical (address lane base source.workHead+distance lane)=decide (source.workHead=0) := by
    rw [address_add_distance]
    exact origin source.workHead
  have fetch := run_shuttle A lanes lane input source physical q (address lane base source.workHead) hi hc
  rw [marker] at fetch
  have fetch' : runFrom ((machine A lanes lane).step input) (embed A lanes lane base source physical)
      (2*distance lane)=some (snapshot A lanes lane source physical
        (some (inward A lanes q (decide (source.workHead=0)) ⟨0, by omega⟩))
        (address lane base source.workHead)) := by
    simpa only [embed, state, Option.map_some] using fetch
  have targetBounds := step_headBounds A input hi hc step
  rw [show 2*distance lane+1+u=2*distance lane+(1+u) by omega, runFrom_add, fetch', Option.bind_some,
    runFrom_add]
  simp only [runFrom_succ, runFrom_zero, Option.bind_some]
  rw [step_apply A lanes lane base input source target physical q state workMatches step]
  exact run_pending_prefix A lanes lane input target _ target.state _ ⟨lanes, by omega⟩ _
    targetBounds.1 targetBounds.2 u hu

/-- Complete transient ledger for one native simulation macro. Before the
unique source action all data are old; afterwards all data are the exact new
source data. No intermediate control can halt. -/
 theorem macro_prefix_spec (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state=some q)
    (hi : source.inputHead ≤ input.length+1) (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : OriginTrack lanes base physical) (workMatches : Matches lane base source.work physical)
    (step : A.step input source=some target) (u : ℕ) (hu : u ≤ macroTime lane)
    (e : Configuration (machine A lanes lane))
    (he : runFrom ((machine A lanes lane).step input) (embed A lanes lane base source physical) u=some e) :
    let a := sourceInstruction A input source q
    let updated := Function.update physical (address lane base source.workHead) a.workWrite
    (e.state≠none ∨ u=macroTime lane) ∧ base ≤ e.workHead ∧
      e.workHead ≤ max (markerAddress lanes base source.workHead) (address lane base target.workHead) ∧
      (DataEq A lanes lane source physical e ∨ DataEq A lanes lane target updated e) := by
  dsimp only
  by_cases hold : u ≤ 2*distance lane
  · obtain ⟨control, head, rfl, hlo, hhi⟩ := shuttle_prefix A lanes lane base input source physical q state hi hc u hold e he
    refine ⟨Or.inl (by simp [snapshot]), ?_, ?_, Or.inl (snapshot_data _ _ _ _ _ _ _)⟩
    · have hb : base ≤ address lane base source.workHead := by dsimp [address]; omega
      change base ≤ head
      omega
    · change head ≤ max _ _
      exact hhi.trans (le_max_left _ _)
  · by_cases hlast : u=macroTime lane
    · subst u
      rw [run_macro A lanes lane base input source target physical q state hi hc origin workMatches step] at he
      cases Option.some.inj he
      refine ⟨Or.inr rfl, ?_, ?_, Or.inr (snapshot_data _ _ _ _ _ _ _)⟩
      · change base ≤ address lane base target.workHead
        dsimp [address]
        omega
      · change address lane base target.workHead ≤ max _ _
        exact le_max_right _ _
    · let v := u-(2*distance lane+1)
      have hv : v < lanes := by dsimp [v, macroTime] at *; omega
      have htime : u=2*distance lane+1+v := by dsimp [v]; omega
      rw [htime, pending_prefix_global A lanes lane base input source target physical q state hi hc origin workMatches step v hv] at he
      cases Option.some.inj he
      have targetEq := ((source_step_spec A input source target q state).mp step).2
      have targetHead : target.workHead=(sourceInstruction A input source q).workMove.apply source.workHead :=
        congrArg (fun c : Configuration A => c.workHead) targetEq
      have between := pending_between lane base source.workHead (sourceInstruction A input source q).workMove v (by omega)
      rw [← targetHead] at between
      refine ⟨Or.inl (by simp [snapshot]), ?_, ?_, Or.inr (snapshot_data _ _ _ _ _ _ _)⟩
      · change base ≤ _
        have hs : base ≤ address lane base source.workHead := by dsimp [address]; omega
        have ht : base ≤ address lane base target.workHead := by dsimp [address]; omega
        exact (le_min hs ht).trans between.1
      · change _ ≤ max _ _
        exact between.2.trans (max_le_max (address_le_marker lane base source.workHead) le_rfl)

 theorem macro_prefix_live (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state=some q)
    (hi : source.inputHead ≤ input.length+1) (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : OriginTrack lanes base physical) (workMatches : Matches lane base source.work physical)
    (step : A.step input source=some target) (u : ℕ) (hu : u < macroTime lane)
    (e : Configuration (machine A lanes lane))
    (he : runFrom ((machine A lanes lane).step input) (embed A lanes lane base source physical) u=some e) :
    e.state≠none := by
  have H := (macro_prefix_spec A lanes lane base input source target physical q state hi hc origin workMatches step u (by omega) e he).1
  exact H.resolve_right (by omega)

 theorem macro_prefix_workHead_bound (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state=some q)
    (hi : source.inputHead ≤ input.length+1) (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : OriginTrack lanes base physical) (workMatches : Matches lane base source.work physical)
    (step : A.step input source=some target) (bound : ℕ)
    (hs : source.workHead < bound) (ht : target.workHead < bound)
    (u : ℕ) (hu : u ≤ macroTime lane) (e : Configuration (machine A lanes lane))
    (he : runFrom ((machine A lanes lane).step input) (embed A lanes lane base source physical) u=some e) :
    base ≤ e.workHead ∧ e.workHead < base+(lanes+1)*bound := by
  have H := macro_prefix_spec A lanes lane base input source target physical q state hi hc origin workMatches step u hu e he
  refine ⟨H.2.1, H.2.2.1.trans_lt ?_⟩
  exact max_lt (marker_lt_prefix lanes base source.workHead bound hs) (address_lt_prefix lane base target.workHead bound ht)

 theorem macro_prefix_data (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : Configuration A) (physical : ℕ → Bool)
    (q : Fin A.states) (state : source.state=some q)
    (hi : source.inputHead ≤ input.length+1) (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : OriginTrack lanes base physical) (workMatches : Matches lane base source.work physical)
    (step : A.step input source=some target) (u : ℕ) (hu : u ≤ macroTime lane)
    (e : Configuration (machine A lanes lane))
    (he : runFrom ((machine A lanes lane).step input) (embed A lanes lane base source physical) u=some e) :
    let a := sourceInstruction A input source q
    let updated := Function.update physical (address lane base source.workHead) a.workWrite
    DataEq A lanes lane source physical e ∨ DataEq A lanes lane target updated e :=
  (macro_prefix_spec A lanes lane base input source target physical q state hi hc origin workMatches step u hu e he).2.2.2

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneFrame -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

theorem Inactive.refl {lanes : ℕ} (lane : Fin lanes) (base : ℕ) (physical : ℕ → Bool) :
    Inactive lane base physical physical := fun _ _ => rfl

theorem Inactive.trans {lanes : ℕ} {lane : Fin lanes} {base : ℕ}
    {a b c : ℕ → Bool} (first : Inactive lane base a b) (second : Inactive lane base b c) :
    Inactive lane base a c := by
  intro p hp
  exact (second p hp).trans (first p hp)

theorem afterWork_inactive (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source : Configuration A) (physical : ℕ → Bool) :
    Inactive lane base physical (afterWork A lanes lane base input source physical) := by
  intro p hp
  cases state : source.state with
  | none => simp only [afterWork, state]
  | some q =>
      simp only [afterWork, state]
      apply Function.update_of_ne
      intro equal
      exact hp ⟨source.workHead, equal.symm⟩

theorem advance_inactive (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) {s t : ValidState A lanes lane base input}
    (step : advance A lanes lane base input s = some t) :
    Inactive lane base s.physical t.physical := by
  unfold advance at step
  split at step <;> cases step
  exact afterWork_inactive A lanes lane base input s.source s.physical

theorem run_inactive (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) {s t : ValidState A lanes lane base input} {n : ℕ}
    (result : runFrom (advance A lanes lane base input) s n = some t) :
    Inactive lane base s.physical t.physical := by
  induction n generalizing t with
  | zero =>
      have equal : s = t := by simpa only [runFrom_zero, Option.some.injEq] using result
      subst t
      exact Inactive.refl lane base s.physical
  | succ n ih =>
      cases hr : runFrom (advance A lanes lane base input) s n with
      | none => simp [runFrom_succ, hr] at result
      | some r =>
          have step : advance A lanes lane base input r = some t := by
            simpa only [runFrom_succ, hr, Option.bind_some] using result
          exact (ih hr).trans (advance_inactive A lanes lane base input step)

theorem frame_embed (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (source current : Configuration A) (physical updated : ℕ → Bool) (F : Footprint)
    (initialMatches : Matches lane base source.work physical)
    (currentMatches : Matches lane base current.work updated)
    (inactive : Inactive lane base physical updated)
    (frame : SameOutside F source current) :
    SameOutside (liftedFootprint lane base F)
      (embed A lanes lane base source physical) (embed A lanes lane base current updated) := by
  refine ⟨?_, frame.2.1, frame.2.2⟩
  intro p hp
  change updated p = physical p
  by_cases active : p ∈ Set.range (address lane base)
  · obtain ⟨q, rfl⟩ := active
    have outside : q ∉ F.work := by
      intro hq
      exact hp ⟨q, hq, rfl⟩
    exact (currentMatches q).trans ((frame.1 q outside).trans (initialMatches q).symm)
  · exact inactive p active

theorem frame_of_data (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (source current : Configuration A) (physical updated : ℕ → Bool) (F : Footprint)
    (initialMatches : Matches lane base source.work physical)
    (currentMatches : Matches lane base current.work updated)
    (inactive : Inactive lane base physical updated)
    (frame : SameOutside F source current) (e : Configuration (machine A lanes lane))
    (data : DataEq A lanes lane current updated e) :
    SameOutside (liftedFootprint lane base F) (embed A lanes lane base source physical) e := by
  have boundary := frame_embed A lanes lane base source current physical updated F
    initialMatches currentMatches inactive frame
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rw [data.1]
    exact boundary.1 p hp
  · rw [data.2.1]
    exact boundary.2.1
  · intro p hp
    rw [data.2.1]
    exact boundary.2.2 p hp

theorem envelope_of_data (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (source : Configuration A) (physical : ℕ → Bool) (E : Envelope)
    (e : Configuration (machine A lanes lane)) (data : DataEq A lanes lane source physical e)
    (heads : base ≤ e.workHead ∧ e.workHead < base + (lanes + 1) * E.workHi)
    (sourceEnvelope : E.Contains source) : (liftedEnvelope lanes base E).Contains e := by
  exact ⟨heads.1, heads.2,
    by simpa only [liftedEnvelope, data.2.2.2.1] using sourceEnvelope.2.2.1,
    by simpa only [liftedEnvelope, data.2.2.2.1] using sourceEnvelope.2.2.2⟩

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneFirstExit -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.WorkLanes

open CatalyticMatching.General

theorem advance_step (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) {s t : ValidState A lanes lane base input}
    (step : advance A lanes lane base input s = some t) :
    A.step input s.source = some t.source := by
  have h := advance_source A lanes lane base input s
  rw [step] at h
  exact h.symm

theorem advance_physical (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) {s t : ValidState A lanes lane base input}
    (step : advance A lanes lane base input s = some t) :
    t.physical = afterWork A lanes lane base input s.source s.physical := by
  unfold advance at step
  split at step <;> cases step
  rfl

theorem source_prefix (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (s : ValidState A lanes lane base input)
    (I : ℕ → Configuration A → Prop) (target : Configuration A) (T : ℕ)
    (H : Segment (A.step input) I s.source target T) (n : ℕ) (hn : n ≤ T) :
    ∃ t, runFrom (advance A lanes lane base input) s n = some t ∧ I n t.source := by
  obtain ⟨c, hc, hi⟩ := H.at hn
  rw [run_source A lanes lane base input s n] at hc
  obtain ⟨t, ht, equal⟩ := Option.map_eq_some_iff.mp hc
  exact ⟨t, ht, by simpa only [equal] using hi⟩

theorem nativeState_data {A : Machine} {lanes : ℕ} {lane : Fin lanes} {base : ℕ}
    {input : List Bool} (s : ValidState A lanes lane base input) :
    DataEq A lanes lane s.source s.physical (nativeState s) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nativeState_envelope {A : Machine} {lanes : ℕ} {lane : Fin lanes} {base : ℕ}
    {input : List Bool} (s : ValidState A lanes lane base input) (E : Envelope)
    (hE : E.Contains s.source) : (liftedEnvelope lanes base E).Contains (nativeState s) := by
  apply envelope_of_data A lanes lane base s.source s.physical E (nativeState s)
    (nativeState_data s) _ hE
  constructor
  · change base ≤ address lane base s.source.workHead
    dsimp [address]
    omega
  · exact address_lt_prefix lane base s.source.workHead E.workHi hE.2.1

/-- A native execution of an arbitrary source subroutine, with every intermediate
configuration charged and framed. The returned physical tape represents the exact
source endpoint and preserves every inactive work lane. -/
theorem firstExit (A : Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (s : ValidState A lanes lane base input)
    (target : Configuration A) (T : ℕ) (E : Envelope) (F : Footprint)
    (H : FirstExit (A.step input)
      (fun _ d => E.Contains d ∧ SameOutside F s.source d)
      {d | d.state = none} s.source target T) :
    ∃ t : ValidState A lanes lane base input,
      t.source = target ∧ Inactive lane base s.physical t.physical ∧
      FirstExit ((machine A lanes lane).step input)
        (fun _ e => (liftedEnvelope lanes base E).Contains e ∧
          SameOutside (liftedFootprint lane base F) (nativeState s) e)
        {e | e.state = none} (nativeState s) (nativeState t) (T * macroTime lane) := by
  have positive : 0 < macroTime lane := by dsimp [macroTime]; omega
  have at_source := source_prefix A lanes lane base input s
    (fun _ d => E.Contains d ∧ SameOutside F s.source d) target T H.toSegment
  obtain ⟨t, ht, tInv⟩ := at_source T le_rfl
  have equal : t.source = target := by
    have result := H.result
    rw [run_source A lanes lane base input s T, ht] at result
    exact Option.some.inj result
  have finalRun : runFrom ((machine A lanes lane).step input) (nativeState s)
      (T * macroTime lane) = some (nativeState t) := by
    rw [run_native A lanes lane base input s T, ht]
    rfl
  have boundary := fun (r : ValidState A lanes lane base input) (n : ℕ)
    (hr : runFrom (advance A lanes lane base input) s n = some r)
    (inv : E.Contains r.source ∧ SameOutside F s.source r.source) =>
      And.intro (nativeState_envelope r E inv.1)
        (frame_embed A lanes lane base s.source r.source s.physical r.physical F
          s.workMatches r.workMatches (run_inactive A lanes lane base input hr) inv.2)
  have interior : ∀ u < T * macroTime lane, ∀ e,
      runFrom ((machine A lanes lane).step input) (nativeState s) u = some e →
      (liftedEnvelope lanes base E).Contains e ∧
        SameOutside (liftedFootprint lane base F) (nativeState s) e ∧ e.state ≠ none := by
    intro u hu e he
    let n := u / macroTime lane
    let r := u % macroTime lane
    have hn : n < T := by
      dsimp [n]
      exact Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hu)
    have hr : r < macroTime lane := Nat.mod_lt u positive
    have decompose : u = n * macroTime lane + r := by
      exact (Nat.div_add_mod' u (macroTime lane)).symm
    obtain ⟨before, hbefore, beforeInv⟩ := at_source n (by omega)
    obtain ⟨after, hafter, afterInv⟩ := at_source (n + 1) (by omega)
    have advanceEq : advance A lanes lane base input before = some after := by
      simpa only [runFrom_succ, hbefore, Option.bind_some] using hafter
    have step := advance_step A lanes lane base input advanceEq
    have sourceRun : runFrom (A.step input) s.source n = some before.source := by
      rw [run_source A lanes lane base input s n, hbefore]
      rfl
    have live : before.source.state ≠ none := H.cut n hn before.source sourceRun
    obtain ⟨q, state⟩ := Option.ne_none_iff_exists'.mp live
    have localRun : runFrom ((machine A lanes lane).step input) (nativeState before) r = some e := by
      rw [decompose, runFrom_add, run_native A lanes lane base input s n, hbefore] at he
      exact he
    have physicalEq : after.physical = Function.update before.physical
        (address lane base before.source.workHead)
        (sourceInstruction A input before.source q).workWrite := by
      simpa only [afterWork, state] using advance_physical A lanes lane base input advanceEq
    have heads := macro_prefix_workHead_bound A lanes lane base input before.source
      after.source before.physical q state before.inputBound before.catalystBound
      before.origin before.workMatches step E.workHi beforeInv.1.2.1 afterInv.1.2.1
      r (by omega) e localRun
    have data := macro_prefix_data A lanes lane base input before.source after.source
      before.physical q state before.inputBound before.catalystBound before.origin
      before.workMatches step r (by omega) e localRun
    have nativeLive := macro_prefix_live A lanes lane base input before.source after.source
      before.physical q state before.inputBound before.catalystBound before.origin
      before.workMatches step r hr e localRun
    rcases data with oldData | newData
    · exact ⟨envelope_of_data A lanes lane base before.source before.physical E e
        oldData heads beforeInv.1,
        frame_of_data A lanes lane base s.source before.source s.physical before.physical F
          s.workMatches before.workMatches (run_inactive A lanes lane base input hbefore)
          beforeInv.2 e oldData, nativeLive⟩
    · rw [← physicalEq] at newData
      exact ⟨envelope_of_data A lanes lane base after.source after.physical E e
        newData heads afterInv.1,
        frame_of_data A lanes lane base s.source after.source s.physical after.physical F
          s.workMatches after.workMatches (run_inactive A lanes lane base input hafter)
          afterInv.2 e newData, nativeLive⟩
  refine ⟨t, equal, run_inactive A lanes lane base input ht, ?_⟩
  refine ⟨⟨finalRun, ?_⟩, ?_, ?_⟩
  · intro u hu e he
    by_cases hlast : u = T * macroTime lane
    · rw [hlast, finalRun] at he
      cases Option.some.inj he
      exact boundary t T ht tInv
    · have data := interior u (by omega) e he
      exact ⟨data.1, data.2.1⟩
  · change (nativeState t).state = none
    have halted : target.state = none := H.exit_mem
    simp only [nativeState, embed, snapshot, equal, halted, Option.map_none]
  · intro u hu e he
    exact (interior u hu e he).2.2

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.WorkLaneCompiler -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.WorkLanes

/-- The full native compiler contract, exposing only physical tapes and source configurations. -/
theorem framed_firstExit (A : CatalyticTreeEval.Main.Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : CatalyticMatching.General.Configuration A)
    (physical : ℕ → Bool) (T : ℕ) (E : CatalyticTreeEval.Contracts.Envelope)
    (F : CatalyticTreeEval.Contracts.Footprint)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : CatalyticTreeEval.Contracts.WorkLanes.OriginTrack lanes base physical)
    (workMatches : CatalyticTreeEval.Contracts.WorkLanes.Matches lane base source.work physical)
    (H : CatalyticTreeEval.Contracts.FirstExit (A.step input)
      (fun _ d => E.Contains d ∧ CatalyticTreeEval.Contracts.SameOutside F source d)
      {d | d.state = none} source target T) :
    ∃ updated : ℕ → Bool,
      CatalyticTreeEval.Contracts.WorkLanes.OriginTrack lanes base updated ∧
      CatalyticTreeEval.Contracts.WorkLanes.Matches lane base target.work updated ∧
      CatalyticTreeEval.Contracts.WorkLanes.Inactive lane base physical updated ∧
      CatalyticTreeEval.Contracts.FirstExit
        ((CatalyticTreeEval.Contracts.WorkLanes.machine A lanes lane).step input)
        (fun _ e => (CatalyticTreeEval.Contracts.WorkLanes.liftedEnvelope lanes base E).Contains e ∧
          CatalyticTreeEval.Contracts.SameOutside
            (CatalyticTreeEval.Contracts.WorkLanes.liftedFootprint lane base F)
            (CatalyticTreeEval.Contracts.WorkLanes.embed A lanes lane base source physical) e)
        {e | e.state = none}
        (CatalyticTreeEval.Contracts.WorkLanes.embed A lanes lane base source physical)
        (CatalyticTreeEval.Contracts.WorkLanes.embed A lanes lane base target updated)
        (T * CatalyticTreeEval.Contracts.WorkLanes.macroTime lane) := by
  let s : ValidState A lanes lane base input := ⟨source, physical, origin, workMatches, hi, hc⟩
  obtain ⟨t, equal, inactive, native⟩ := firstExit A lanes lane base input s target T E F H
  refine ⟨t.physical, t.origin, ?_, inactive, ?_⟩
  · simpa only [equal] using t.workMatches
  · simpa only [nativeState, s, equal] using native

end CatalyticTreeEval.Contracts.WorkLanes
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeRunHeadBounds -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts

open CatalyticMatching.General

/-- Successful arbitrary-start runs preserve the physical input/catalyst head
bounds enforced by the original native step semantics. -/
theorem runFrom_headBounds (M : Machine) (input : List Bool) (c : Configuration M)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    {d : Configuration M} {n : ℕ} (result : runFrom (M.step input) c n = some d) :
    d.inputHead ≤ input.length+1 ∧ d.catalystHead ≤ d.catalyst.length := by
  induction n generalizing d with
  | zero =>
    cases Option.some.inj result
    exact ⟨hi, hc⟩
  | succ n ih =>
    cases hr : runFrom (M.step input) c n with
    | none => simp [runFrom_succ, hr] at result
    | some e =>
      have last : M.step input e = some d := by
        simpa only [runFrom_succ, hr, Option.bind_some] using result
      exact step_headBounds M input (ih hr).1 (ih hr).2 last

end CatalyticTreeEval.Contracts
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeLaneBoundedLift -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeRoundSupport

/-- Arithmetic routines export a work bound and a physical memory frame. Their
successful native prefixes also give the remaining source head bounds required
by the proved lane compiler; no new simulator hypothesis is introduced. -/
theorem firstExit_envelope {A : Main.Machine} (input : List Bool) (c d : Config A)
    (time bound : ℕ) (F : Footprint)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (H : FirstExit (A.step input) (fun _ e => e.workHead < bound ∧ Frame F c e)
      {e | e.state = none} c d time) :
    FirstExit (A.step input)
      (fun _ e => (Envelope.mk 0 bound 0 (c.catalyst.length + 1)).Contains e ∧ SameOutside F c e)
      {e | e.state = none} c d time := by
  refine { result := H.result, exit_mem := H.exit_mem, cut := H.cut, during := ?_ }
  intro u hu e he
  have HB := runFrom_headBounds A input c hi hc he
  have HF := H.during u hu e he
  refine ⟨?_,HF.2⟩
  change 0 ≤ e.workHead ∧ e.workHead < bound ∧ 0 ≤ e.catalystHead ∧ e.catalystHead < c.catalyst.length + 1
  have hlen := HF.2.2.1
  omega

theorem bounded_firstExit (A : Main.Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : Config A) (physical : ℕ → Bool)
    (time bound : ℕ) (F : Footprint)
    (hi : source.inputHead ≤ input.length + 1) (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : WorkLanes.OriginTrack lanes base physical)
    (workMatches : WorkLanes.Matches lane base source.work physical)
    (H : FirstExit (A.step input) (fun _ e => e.workHead < bound ∧ Frame F source e)
      {e | e.state = none} source target time) :
    ∃ updated : ℕ → Bool,
      WorkLanes.OriginTrack lanes base updated ∧ WorkLanes.Matches lane base target.work updated ∧
      WorkLanes.Inactive lane base physical updated ∧
      FirstExit ((WorkLanes.machine A lanes lane).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * bound ∧
          SameOutside (WorkLanes.liftedFootprint lane base F)
            (WorkLanes.embed A lanes lane base source physical) e)
        {e | e.state = none} (WorkLanes.embed A lanes lane base source physical)
        (WorkLanes.embed A lanes lane base target updated) (time * WorkLanes.macroTime lane) := by
  have HE := firstExit_envelope input source target time bound F hi hc H
  obtain ⟨updated,horigin,hmatches,hinactive,Hnative⟩ := WorkLanes.framed_firstExit A lanes lane base input
    source target physical time (Envelope.mk 0 bound 0 (source.catalyst.length + 1)) F hi hc origin workMatches HE
  refine ⟨updated,horigin,hmatches,hinactive,?_⟩
  exact
    { result := Hnative.result
      during := fun u hu e he => ⟨(Hnative.during u hu e he).1.2.1,(Hnative.during u hu e he).2⟩
      exit_mem := Hnative.exit_mem
      cut := Hnative.cut }

end CatalyticTreeEval.Contracts.NativeRoundSupport
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeMSBLiftPort -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeMSBFold

open NativeRoundSupport

theorem embed_sameIO {N : Main.Machine} {lanes : ℕ} (A : Main.Machine) (lane : Fin lanes)
    (base : ℕ) (c : Config N) (target : Config A) (updated : ℕ → Bool)
    (H : RestoringRound.SameIO (logicalStart A lane base c) target) :
    RestoringRound.SameIO c (WorkLanes.embed A lanes lane base target updated) := by
  simpa [RestoringRound.SameIO,logicalStart,WorkLanes.embed,WorkLanes.snapshot] using H

theorem inactive_other_lane {lanes : ℕ} (lane other : Fin lanes) (base : ℕ)
    (initial updated : ℕ → Bool) (H : WorkLanes.Inactive lane base initial updated) (hne : other ≠ lane) :
    ∀ p, updated (WorkLanes.address other base p) = initial (WorkLanes.address other base p) := by
  intro p
  apply H
  rintro ⟨q,he⟩
  exact hne (WorkLanes.address_lanes_injective other lane base p q he.symm).1

/-- Invoke an existing native arithmetic leaf in one physical work lane, from
the real caller's flag. The execution and all frames come from the checked lane
compiler applied to that leaf's actual source FirstExit certificate. -/
theorem lift_port {N : Main.Machine} {lanes : ℕ} (A : Main.Machine) (lane : Fin lanes)
    (input : List Bool) (c : Config N) (base : ℕ) (target : Config A) (time bound : ℕ) (F : Footprint)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (origin : WorkLanes.OriginTrack lanes base c.work) (hhead : c.workHead = base + lane.val)
    (H : FirstExit (A.step input)
      (fun _ e => e.workHead < bound ∧ Frame F (logicalStart A lane base c) e)
      {e | e.state = none} (logicalStart A lane base c) target time) :
    ∃ updated : ℕ → Bool,
      WorkLanes.OriginTrack lanes base updated ∧ WorkLanes.Matches lane base target.work updated ∧
      WorkLanes.Inactive lane base c.work updated ∧
      FirstExit ((WorkLanes.machine A lanes lane).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * bound ∧
          Frame (WorkLanes.liftedFootprint lane base F) c e)
        {e | e.state = none} (startOn (WorkLanes.machine A lanes lane) c)
        (WorkLanes.embed A lanes lane base target updated) (time * WorkLanes.macroTime lane) := by
  obtain ⟨updated,horigin,hmatches,hinactive,Hnative⟩ := bounded_firstExit A lanes lane base input
    (logicalStart A lane base c) target c.work time bound F hi hc origin (logicalStart_matches A lane base c) H
  have hentry := embed_logicalStart A lane base c hhead
  rw [hentry] at Hnative
  refine ⟨updated,horigin,hmatches,hinactive,?_⟩
  exact
    { result := Hnative.result
      during := fun u hu e he => ⟨(Hnative.during u hu e he).1,(Hnative.during u hu e he).2⟩
      exit_mem := Hnative.exit_mem
      cut := Hnative.cut }

end CatalyticTreeEval.Contracts.NativeMSBFold
end

/- Proof component: Solutions.CatalyticTreeEvaluation.ConsumeMSB -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.ConsumeMSB

open NativeRoundSupport
open RestoringRound (SameIO)

theorem machine_states : machine.states = 30 := by decide

theorem saveCarry_exec {N : Main.Machine} (input : List Bool) (c : Config N)
    (base width : ℕ) (bit : Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base + 6 + 3 * width)
    (hmarker : c.work (base + 3) = false)
    (htags : ∀ i < width, c.work (base + 6 + 3 * i) = true) :
    ∃ d : Config (saveCarry bit),
      FirstExit ((saveCarry bit).step input) (fun _ _ => True) {d | d.state = none}
        (startOn (saveCarry bit) c) d (3 * width + 8) ∧
      Visits input (startOn (saveCarry bit) c) (3 * width + 8)
        (base + 6 + 3 * width + 1) ∧
      Frames input c (startOn (saveCarry bit) c) (3 * width + 8)
        ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ ∧
      d.workHead = base ∧
      d.work = Function.update (Function.update c.work (base + 6 + 3 * width) false) base bit ∧
      SameIO c d := by
  let C := NativeLiteral.machine .stay 0 (some false)
  let W := NativeLiteral.machine .stay 0 (some bit)
  let cc := startOn C c
  let dc := NativeLiteral.finished .stay 0 (some false) cc
  have HC0 := NativeLiteral.firstExit .stay 0 (some false) input cc hi hc
  have HC : FirstExit (C.step input) (fun _ _ => True) {d | d.state = none} cc dc 1 := by
    simpa [C, cc, dc, NativeLiteral.live, NativeLiteral.position, startOn,
      NativeLiteral.machine] using forget HC0
  have VC : Visits input cc 1 (base + 6 + 3 * width + 1) := by
    simpa [C, cc, NativeLiteral.live, NativeLiteral.position, startOn,
      NativeLiteral.machine] using
      visits_of_envelope HC0 (bound := base + 6 + 3 * width + 1) (by
        dsimp [cc, startOn]; omega)
  have hcw : dc.work = Function.update c.work (base + 6 + 3 * width) false := by
    simp [dc, cc, C, NativeLiteral.finished, NativeLiteral.position, hhead, startOn]
  have FC : Frames input c cc 1 ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ := by
    apply (frames_of_contract HC0).mono
    · intro p hp
      have he : p = c.workHead := by simpa [cc, startOn, NativeLiteral.position] using hp
      subst p
      constructor <;> omega
    · exact Set.Subset.refl _
  have hch : dc.workHead = base + 6 + 3 * width := by
    simp [dc, cc, C, NativeLiteral.finished, NativeLiteral.position, hhead, startOn]
  have hcm : dc.work (base + 3) = false := by
    rw [hcw, Function.update_of_ne (by omega : base + 3 ≠ base + 6 + 3 * width)]
    exact hmarker
  have hct : ∀ i < width, dc.work (base + 6 + 3 * i) = true := by
    intro i hiw
    rw [hcw, Function.update_of_ne (by omega : base + 6 + 3 * i ≠ base + 6 + 3 * width)]
    exact htags i hiw
  let cr := startOn (TaggedRewind.machine false) dc
  let dr := TaggedRewind.cursor cr base none
  have HR0 := TaggedRewind.firstExit input cr base width hi hc hcm hct
  have HR : FirstExit ((TaggedRewind.machine false).step input) (fun _ _ => True)
      {d | d.state = none} cr dr (3 * width + 6) := by
    simpa [cr, dr, TaggedRewind.leftCursor, TaggedRewind.cursor, hch, startOn,
      TaggedRewind.machine] using forget HR0
  have VR : Visits input cr (3 * width + 6) (base + 6 + 3 * width + 1) := by
    simpa [cr, TaggedRewind.leftCursor, TaggedRewind.cursor, hch, startOn,
      TaggedRewind.machine] using
      visits_of_envelope HR0 (bound := base + 6 + 3 * width + 1) le_rfl
  have FR : Frames input dc cr (3 * width + 6)
      ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ := by
    have F := (frames_of_contract HR0).mono
      (G := ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩)
      (show TaggedRewind.footprint.work ⊆ Set.Ico base (base + 6 + 3 * width + 1) by simp [TaggedRewind.footprint])
      (show TaggedRewind.footprint.catalyst ⊆ (∅ : Set ℕ) by simp [TaggedRewind.footprint])
    simpa [Frames, Frame, cr, TaggedRewind.leftCursor, TaggedRewind.cursor, hch, startOn,
      TaggedRewind.machine] using F
  let cw := startOn W dr
  let dw := NativeLiteral.finished .stay 0 (some bit) cw
  have HW0 := NativeLiteral.firstExit .stay 0 (some bit) input cw hi hc
  have HW : FirstExit (W.step input) (fun _ _ => True) {d | d.state = none} cw dw 1 := by
    simpa [W, cw, dw, NativeLiteral.live, NativeLiteral.position, startOn,
      NativeLiteral.machine] using forget HW0
  have VW : Visits input cw 1 (base + 6 + 3 * width + 1) := by
    simpa [W, cw, NativeLiteral.live, NativeLiteral.position, startOn,
      NativeLiteral.machine] using
      visits_of_envelope HW0 (bound := base + 6 + 3 * width + 1) (by
        dsimp [cw, dr, TaggedRewind.cursor, startOn]; omega)
  have FW : Frames input dr cw 1 ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ := by
    apply (frames_of_contract HW0).mono
    · intro p hp
      have he : p = base := by simpa [cw, dr, TaggedRewind.cursor, startOn, NativeLiteral.position] using hp
      subst p
      constructor <;> omega
    · exact Set.Subset.refl _
  have HRW := seq (TaggedRewind.machine false) W input dc dr dw (3 * width + 6) 1 HR HW
  have VRW := visits_seq (TaggedRewind.machine false) W input dc dr dw (3 * width + 6) 1
    (base + 6 + 3 * width + 1) HR HW VR VW
  have FRW := frames_seq (TaggedRewind.machine false) W input dc dr dw (3 * width + 6) 1
    ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ HR HW FR FW
  have H := seq C (Sequential.machine (TaggedRewind.machine false) W) input c dc
    (Sequential.rightConfig (TaggedRewind.machine false) W dw) 1 (3 * width + 6 + 1) HC HRW
  have V := visits_seq C (Sequential.machine (TaggedRewind.machine false) W) input c dc
    (Sequential.rightConfig (TaggedRewind.machine false) W dw) 1 (3 * width + 6 + 1)
    (base + 6 + 3 * width + 1) HC HRW VC VRW
  have F := frames_seq C (Sequential.machine (TaggedRewind.machine false) W) input c dc
    (Sequential.rightConfig (TaggedRewind.machine false) W dw) 1 (3 * width + 6 + 1)
    ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ HC HRW FC FRW
  let d := Sequential.rightConfig C (Sequential.machine (TaggedRewind.machine false) W)
    (Sequential.rightConfig (TaggedRewind.machine false) W dw)
  refine ⟨d, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · simpa only [saveCarry, C, W, show 1 + (3 * width + 6 + 1) = 3 * width + 8 by omega] using H
  · simpa only [saveCarry, C, W, show 1 + (3 * width + 6 + 1) = 3 * width + 8 by omega] using V
  · simpa only [saveCarry, C, W, show 1 + (3 * width + 6 + 1) = 3 * width + 8 by omega] using F
  · change dw.work = _
    simp only [dw, cw, dr, cr, NativeLiteral.finished, NativeLiteral.position,
      TaggedRewind.cursor, startOn]
    exact congrArg (fun work => Function.update work base bit) hcw
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem carryDispatch_exec {N : Main.Machine} (input : List Bool) (c : Config N)
    (base width : ℕ)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base + 6 + 3 * width)
    (hmarker : c.work (base + 3) = false)
    (htags : ∀ i < width, c.work (base + 6 + 3 * i) = true) :
    ∃ d : Config carryDispatch,
      FirstExit (carryDispatch.step input) (fun _ _ => True) {d | d.state = none}
        (startOn carryDispatch c) d (3 * width + 9) ∧
      Visits input (startOn carryDispatch c) (3 * width + 9)
        (base + 6 + 3 * width + 1) ∧
      Frames input c (startOn carryDispatch c) (3 * width + 9)
        ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ ∧
      d.workHead = base ∧
      d.work = Function.update (Function.update c.work (base + 6 + 3 * width) false)
        base (c.work (base + 6 + 3 * width)) ∧ SameIO c d := by
  cases hb : c.work (base + 6 + 3 * width) with
  | true =>
    obtain ⟨d, H, V, F, hh, hw, hIO⟩ := saveCarry_exec input c base width true hi hc hhead hmarker htags
    have HE := branch_true (saveCarry true) (saveCarry false) input c d (3 * width + 8)
      (by rw [hhead, hb]) hi hc H
    have VE := visits_branch_true (saveCarry true) (saveCarry false) input c d (3 * width + 8)
      (base + 6 + 3 * width + 1) (by rw [hhead, hb]) hi hc H (by omega) V
    have FE := frames_branch_true (saveCarry true) (saveCarry false) input c d (3 * width + 8)
      ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ (by rw [hhead, hb]) hi hc H F
    refine ⟨Branch.leftConfig (saveCarry true) (saveCarry false) d, ?_, ?_, ?_, hh, ?_, hIO⟩
    · simpa only [carryDispatch, show 1 + (3 * width + 8) = 3 * width + 9 by omega] using HE
    · simpa only [carryDispatch, show 1 + (3 * width + 8) = 3 * width + 9 by omega] using VE
    · simpa only [carryDispatch, show 1 + (3 * width + 8) = 3 * width + 9 by omega] using FE
    · simpa only [Branch.leftConfig, hb] using hw
  | false =>
    obtain ⟨d, H, V, F, hh, hw, hIO⟩ := saveCarry_exec input c base width false hi hc hhead hmarker htags
    have HE := branch_false (saveCarry true) (saveCarry false) input c d (3 * width + 8)
      (by rw [hhead, hb]) hi hc H
    have VE := visits_branch_false (saveCarry true) (saveCarry false) input c d (3 * width + 8)
      (base + 6 + 3 * width + 1) (by rw [hhead, hb]) hi hc H (by omega) V
    have FE := frames_branch_false (saveCarry true) (saveCarry false) input c d (3 * width + 8)
      ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ (by rw [hhead, hb]) hi hc H F
    refine ⟨Branch.rightConfig (saveCarry true) (saveCarry false) d, ?_, ?_, ?_, hh, ?_, hIO⟩
    · simpa only [carryDispatch, show 1 + (3 * width + 8) = 3 * width + 9 by omega] using HE
    · simpa only [carryDispatch, show 1 + (3 * width + 8) = 3 * width + 9 by omega] using VE
    · simpa only [carryDispatch, show 1 + (3 * width + 8) = 3 * width + 9 by omega] using FE
    · simpa only [Branch.rightConfig, hb] using hw

theorem bank_exec {N : Main.Machine} (input : List Bool) (c : Config N)
    (base width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base + 6) (hmarker : c.work (base + 3) = false)
    (hbank : ShiftAppend.bankContents c.work (base + 6) width a b) :
    ∃ d : Config (Sequential.machine ShiftAppend.machine carryDispatch),
      FirstExit ((Sequential.machine ShiftAppend.machine carryDispatch).step input)
        (fun _ _ => True) {d | d.state = none}
        (startOn (Sequential.machine ShiftAppend.machine carryDispatch) c) d (6 * width + 10) ∧
      Visits input (startOn (Sequential.machine ShiftAppend.machine carryDispatch) c)
        (6 * width + 10) (base + 6 + 3 * width + 1) ∧
      Frames input c (startOn (Sequential.machine ShiftAppend.machine carryDispatch) c)
        (6 * width + 10) ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ ∧
      d.workHead = base ∧
      d.work = Function.update
        (Function.update (ShiftAppend.prefixWork c.work (base + 6) a b false width)
          (base + 6 + 3 * width) false) base (ShiftAppend.carryAt a b false width) ∧
      SameIO c d := by
  let cs := startOn ShiftAppend.machine c
  let ds := ShiftAppend.finished cs (base + 6) width a b false
  have HS0 := ShiftAppend.bank_firstExit input cs (base + 6) width a b false hi hc hbank
  have HS : FirstExit (ShiftAppend.machine.step input) (fun _ _ => True) {d | d.state = none}
      cs ds (3 * width + 1) := by
    simpa [cs, ds, ShiftAppend.cursor, hhead, startOn, ShiftAppend.machine,
      ShiftAppend.marker] using forget HS0
  have VS : Visits input cs (3 * width + 1) (base + 6 + 3 * width + 1) := by
    simpa [cs, ShiftAppend.cursor, hhead, startOn, ShiftAppend.machine,
      ShiftAppend.marker] using
      visits_of_envelope HS0 (bound := base + 6 + 3 * width + 1) le_rfl
  have hdm : ds.work (base + 3) = false := by
    exact ((HS0.during (3 * width + 1) le_rfl ds HS0.result).2.1
      (base + 3) (by simp only [Set.mem_Ico]; omega)).trans hmarker
  have FS : Frames input c cs (3 * width + 1)
      ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ := by
    have F := (frames_of_contract HS0).mono
      (G := ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩)
      (show Set.Ico (base + 6) (base + 6 + 3 * width + 1) ⊆
        Set.Ico base (base + 6 + 3 * width + 1) by
          intro p hp
          rcases hp with ⟨hp1, hp2⟩
          constructor <;> omega)
      (Set.Subset.refl _)
    simpa [Frames, Frame, cs, ShiftAppend.cursor, hhead, startOn, ShiftAppend.machine, ShiftAppend.marker] using F
  have hdt : ∀ i < width, ds.work (base + 6 + 3 * i) = true := by
    intro i hiw
    have hne : base + 6 + 3 * i ≠ base + 6 + 3 * width := by omega
    change Function.update (ShiftAppend.prefixWork cs.work (base + 6) a b false width)
      (base + 6 + 3 * width) (ShiftAppend.carryAt a b false width) (base + 6 + 3 * i) = true
    rw [Function.update_of_ne hne, ShiftAppend.prefixWork_marker]
    exact (hbank.2 i hiw).1
  obtain ⟨dd, HD, VD, FD, hdh, hdw, hdIO⟩ := carryDispatch_exec input ds base width hi hc rfl hdm hdt
  have H := seq ShiftAppend.machine carryDispatch input c ds dd (3 * width + 1)
    (3 * width + 9) HS HD
  have V := visits_seq ShiftAppend.machine carryDispatch input c ds dd (3 * width + 1)
    (3 * width + 9) (base + 6 + 3 * width + 1) HS HD VS VD
  have F := frames_seq ShiftAppend.machine carryDispatch input c ds dd (3 * width + 1)
    (3 * width + 9) ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ HS HD FS FD
  refine ⟨Sequential.rightConfig ShiftAppend.machine carryDispatch dd, ?_, ?_, ?_, hdh, ?_, hdIO⟩
  · simpa only [show 3 * width + 1 + (3 * width + 9) = 6 * width + 10 by omega] using H
  · simpa only [show 3 * width + 1 + (3 * width + 9) = 6 * width + 10 by omega] using V
  · simpa only [show 3 * width + 1 + (3 * width + 9) = 6 * width + 10 by omega] using F
  · change dd.work = _
    rw [hdw]
    simp only [ds, cs, ShiftAppend.finished, startOn, Function.update_self,
      Function.update_idem]

/-- The complete fixed native MSB consumer takes exactly `6*width+17`
transitions. Its final carry is false, and the saved bit occupies the ABI flag.
Every intermediate work-head address is charged, including the terminal cell. -/
theorem machine_exec {N : Main.Machine} (input : List Bool) (c : Config N)
    (base width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base) (hmarker : c.work (base + 3) = false)
    (hbank : ShiftAppend.bankContents c.work (base + 6) width a b) :
    ∃ d : Config machine,
      FirstExit (machine.step input)
        (fun _ e => e.workHead < base + 6 + 3 * width + 1 ∧
          Frame ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ c e) {d | d.state = none}
        (startOn machine c) d (6 * width + 17) ∧
      d.workHead = base ∧
      d.work = Function.update
        (Function.update (ShiftAppend.prefixWork c.work (base + 6) a b false width)
          (base + 6 + 3 * width) false) base (ShiftAppend.carryAt a b false width) ∧
      SameIO c d := by
  let M := NativeLiteral.machine .right 6 none
  let cm := startOn M c
  let dm := NativeLiteral.finished .right 6 none cm
  have HM0 := NativeLiteral.firstExit .right 6 none input cm hi hc
  have HM : FirstExit (M.step input) (fun _ _ => True) {d | d.state = none} cm dm 7 := by
    simpa [M, cm, dm, NativeLiteral.live, NativeLiteral.position, startOn,
      NativeLiteral.machine] using forget HM0
  have VM : Visits input cm 7 (base + 6 + 3 * width + 1) := by
    simpa [M, cm, NativeLiteral.live, NativeLiteral.position, startOn,
      NativeLiteral.machine] using
      visits_of_envelope HM0 (bound := base + 6 + 3 * width + 1) (by
        dsimp [cm, startOn]; omega)
  have hmh : dm.workHead = base + 6 := by
    simp [dm, cm, NativeLiteral.finished, NativeLiteral.position_right, hhead, startOn]
  have hmw : dm.work = c.work := by
    simp [dm, cm, NativeLiteral.finished, startOn, Function.update_eq_self]
  have FM : Frames input c cm 7 ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ := by
    apply (frames_of_contract HM0).mono
    · intro p hp
      have he : p = base + 6 := by simpa [cm, startOn, NativeLiteral.position_right, hhead] using hp
      subst p
      constructor <;> omega
    · exact Set.Subset.refl _
  obtain ⟨db, HB, VB, FB, hbh, hbw, hbIO⟩ := bank_exec input dm base width a b hi hc hmh
    (by rw [hmw]; exact hmarker) (by rw [hmw]; exact hbank)
  have H := seq M (Sequential.machine ShiftAppend.machine carryDispatch) input c dm db
    7 (6 * width + 10) HM HB
  have V := visits_seq M (Sequential.machine ShiftAppend.machine carryDispatch) input c dm db
    7 (6 * width + 10) (base + 6 + 3 * width + 1) HM HB VM VB
  have F := frames_seq M (Sequential.machine ShiftAppend.machine carryDispatch) input c dm db
    7 (6 * width + 10) ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ HM HB FM FB
  let d := Sequential.rightConfig M (Sequential.machine ShiftAppend.machine carryDispatch) db
  have H' : FirstExit (machine.step input) (fun _ _ => True) {d | d.state = none}
      (startOn machine c) d (6 * width + 17) := by
    simpa only [machine, M, show 7 + (6 * width + 10) = 6 * width + 17 by omega] using H
  have V' : Visits input (startOn machine c) (6 * width + 17)
      (base + 6 + 3 * width + 1) := by
    simpa only [machine, M, show 7 + (6 * width + 10) = 6 * width + 17 by omega] using V
  have F' : Frames input c (startOn machine c) (6 * width + 17)
      ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ := by
    simpa only [machine, M, show 7 + (6 * width + 10) = 6 * width + 17 by omega] using F
  have HF : FirstExit (machine.step input)
      (fun _ e => e.workHead < base + 6 + 3 * width + 1 ∧
        Frame ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ c e)
      {d | d.state = none} (startOn machine c) d (6 * width + 17) :=
    { result := H'.result
      during := fun u hu e he => ⟨V' u hu e he, F' u hu e he⟩
      exit_mem := H'.exit_mem
      cut := H'.cut }
  refine ⟨d, HF, hbh, ?_, hbIO⟩
  change db.work = _
  simpa only [hmw] using hbw

end CatalyticTreeEval.Contracts.ConsumeMSB
end

/- Proof component: Solutions.CatalyticTreeEvaluation.ConsumeMSBArithmetic -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.ConsumeMSB

open NativeRoundSupport
open RestoringRound (SameIO)

theorem carryAt_succ (a b : ℕ → Bool) (initial : Bool) (n : ℕ) :
    ShiftAppend.carryAt a b initial (n + 1) = a n := rfl

theorem final_bank (work : ℕ → Bool) (base width : ℕ) (a b : ℕ → Bool)
    (hbank : ShiftAppend.bankContents work (base + 6) width a b) :
    ShiftAppend.bankContents
      (Function.update
        (Function.update (ShiftAppend.prefixWork work (base + 6) a b false width)
          (base + 6 + 3 * width) false) base (ShiftAppend.carryAt a b false width))
      (base + 6) width (ShiftAppend.sumAt a b false) b := by
  constructor
  · rw [Function.update_of_ne (by omega : base + 6 + 3 * width ≠ base), Function.update_self]
  · intro i hiw
    have ht : base + 6 + 3 * i ≠ base + 6 + 3 * width := by omega
    have ha : base + 6 + 3 * i + 1 ≠ base + 6 + 3 * width := by omega
    have hb : base + 6 + 3 * i + 2 ≠ base + 6 + 3 * width := by omega
    simp only [Function.update_of_ne (by omega : base + 6 + 3 * i ≠ base),
      Function.update_of_ne (by omega : base + 6 + 3 * i + 1 ≠ base),
      Function.update_of_ne (by omega : base + 6 + 3 * i + 2 ≠ base),
      Function.update_of_ne ht, Function.update_of_ne ha, Function.update_of_ne hb,
      ShiftAppend.prefixWork_marker, ShiftAppend.prefixWork_a,
      ShiftAppend.prefixWork_b, if_pos hiw]
    exact ⟨(hbank.2 i hiw).1, True.intro, (hbank.2 i hiw).2.2⟩

/-- Native term-stream consumption with its exact arithmetic equation. The
output flag is the old A-bank MSB, the remaining bank is doubled modulo its
capacity, and the B bank is physically preserved. -/
theorem machine_arithmetic {N : Main.Machine} (input : List Bool) (c : Config N)
    (base width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = base) (hmarker : c.work (base + 3) = false)
    (hbank : ShiftAppend.bankContents c.work (base + 6) width a b) :
    ∃ d : Config machine,
      FirstExit (machine.step input)
        (fun _ e => e.workHead < base + 6 + 3 * width + 1 ∧
          Frame ⟨Set.Ico base (base + 6 + 3 * width + 1), ∅⟩ c e) {d | d.state = none}
        (startOn machine c) d (6 * width + 17) ∧
      d.workHead = base ∧ d.work base = ShiftAppend.carryAt a b false width ∧
      ShiftAppend.bankContents d.work (base + 6) width (ShiftAppend.sumAt a b false) b ∧
      ShiftAppend.bankValue (fun i => d.work (base + 6 + 3 * i + 1)) width +
        2 ^ width * (d.work base).toNat = 2 * ShiftAppend.bankValue a width ∧
      d.work (base + 3) = false ∧
      (∀ position, position ∉ insert base (Set.Ico (base + 6) (base + 6 + 3 * width + 1)) →
        d.work position = c.work position) ∧ SameIO c d := by
  obtain ⟨d, H, hdh, hdw, hdIO⟩ := machine_exec input c base width a b hi hc hhead hmarker hbank
  have hflag : d.work base = ShiftAppend.carryAt a b false width := by
    rw [hdw, Function.update_self]
  have hdb : ShiftAppend.bankContents d.work (base + 6) width (ShiftAppend.sumAt a b false) b := by
    rw [hdw]
    exact final_bank c.work base width a b hbank
  refine ⟨d, H, hdh, hflag, hdb, ?_, ?_, ?_, hdIO⟩
  · have hval : ShiftAppend.bankValue (fun i => d.work (base + 6 + 3 * i + 1)) width =
        ShiftAppend.bankValue (ShiftAppend.sumAt a b false) width := by
      unfold ShiftAppend.bankValue
      apply Finset.sum_congr rfl
      intro i hiw
      dsimp only
      rw [(hdb.2 i (Finset.mem_range.mp hiw)).2.1]
    rw [hval, hflag]
    simpa using ShiftAppend.bankValue_append a b false width
  · rw [hdw, Function.update_of_ne (by omega : base + 3 ≠ base),
      Function.update_of_ne (by omega : base + 3 ≠ base + 6 + 3 * width)]
    rw [ShiftAppend.prefixWork_outside c.work (base + 6) width a b false width le_rfl
      (base + 3) (by simp only [Set.mem_Ico]; omega)]
    exact hmarker
  · intro position hp
    have hpbase : position ≠ base := by intro h; apply hp; exact Set.mem_insert_iff.mpr (Or.inl h)
    have hpbank : position ∉ Set.Ico (base + 6) (base + 6 + 3 * width + 1) := by
      intro h; apply hp; exact Set.mem_insert_iff.mpr (Or.inr h)
    have hptop : position ≠ base + 6 + 3 * width := by
      intro h; apply hpbank; subst position; constructor <;> omega
    rw [hdw, Function.update_of_ne hpbase, Function.update_of_ne hptop]
    exact ShiftAppend.prefixWork_outside c.work (base + 6) width a b false width le_rfl position hpbank

end CatalyticTreeEval.Contracts.ConsumeMSB
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeMSBConsumePort -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeMSBFold

open NativeRoundSupport
open RestoringRound (SameIO)

def laneBank {lanes : ℕ} (lane : Fin lanes) (base width : ℕ)
    (work a b : ℕ → Bool) : Prop :=
  ShiftAppend.bankContents (fun p => work (WorkLanes.address lane base p)) 6 width a b

theorem consume_exec {N : Main.Machine} {lanes : ℕ} (lane : Fin lanes)
    (input : List Bool) (c : Config N) (base width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (origin : WorkLanes.OriginTrack lanes base c.work) (hhead : c.workHead = base + lane.val)
    (hmarker : c.work (WorkLanes.address lane base 3) = false)
    (hbank : laneBank lane base width c.work a b) :
    ∃ d : Config (WorkLanes.machine ConsumeMSB.machine lanes lane),
      FirstExit ((WorkLanes.machine ConsumeMSB.machine lanes lane).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * (7 + 3 * width) ∧
          Frame (WorkLanes.liftedFootprint lane base ⟨Set.Ico 0 (7 + 3 * width),∅⟩) c e)
        {e | e.state = none} (startOn (WorkLanes.machine ConsumeMSB.machine lanes lane) c) d
        ((6 * width + 17) * WorkLanes.macroTime lane) ∧
      d.workHead = base + lane.val ∧ WorkLanes.OriginTrack lanes base d.work ∧
      WorkLanes.Inactive lane base c.work d.work ∧
      d.work (WorkLanes.address lane base 0) = ShiftAppend.carryAt a b false width ∧
      laneBank lane base width d.work (ShiftAppend.sumAt a b false) b ∧
      d.work (WorkLanes.address lane base 3) = false ∧ SameIO c d := by
  let A := ConsumeMSB.machine
  let s := logicalStart A lane base c
  obtain ⟨target,HS,hth,htf,htbank,_,htmarker,_,htIO⟩ := ConsumeMSB.machine_arithmetic input s 0 width a b hi hc rfl hmarker hbank
  have Hsource : FirstExit (A.step input)
      (fun _ e => e.workHead < 7 + 3 * width ∧ Frame ⟨Set.Ico 0 (7 + 3 * width),∅⟩ s e)
      {e | e.state = none} s target (6 * width + 17) := by
    simpa [A,s,logicalStart,startOn,show 6 + 3 * width + 1 = 7 + 3 * width by omega] using HS
  obtain ⟨updated,horigin,hmatches,hinactive,Hnative⟩ := lift_port A lane input c base target (6 * width + 17)
    (7 + 3 * width) ⟨Set.Ico 0 (7 + 3 * width),∅⟩ hi hc origin hhead Hsource
  let d := WorkLanes.embed A lanes lane base target updated
  have hwork : (fun p => updated (WorkLanes.address lane base p)) = target.work := funext hmatches
  refine ⟨d,Hnative,?_,horigin,hinactive,?_,?_,?_,embed_sameIO A lane base c target updated htIO⟩
  · simp [d,WorkLanes.embed,WorkLanes.snapshot,hth,WorkLanes.address]
  · exact (hmatches 0).trans htf
  · change ShiftAppend.bankContents (fun p => updated (WorkLanes.address lane base p)) 6 width (ShiftAppend.sumAt a b false) b
    rw [hwork]
    exact htbank
  · exact (hmatches 3).trans htmarker

end CatalyticTreeEval.Contracts.NativeMSBFold
end

/- Proof component: Solutions.CatalyticTreeEvaluation.BinaryCountdown -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinaryCountdown

open CatalyticMatching.General

theorem subtract_bit (borrow a : Bool) :
    (resultBit borrow a).toNat + borrow.toNat = a.toNat + 2 * (nextBorrow borrow a).toNat := by
  cases borrow <;> cases a <;> decide

theorem bankValue_lt (bits : ℕ → Bool) (width : ℕ) : bankValue bits width < 2 ^ width := by
  induction width with
  | zero => simp [bankValue]
  | succ width ih =>
      have hbit : (bits width).toNat ≤ 1 := by cases bits width <;> decide
      have hbound := Nat.mul_le_mul_right (2 ^ width) hbit
      simp only [bankValue, Finset.sum_range_succ, pow_succ] at *
      nlinarith [Nat.two_pow_pos width]

theorem bankValue_decrement (a : ℕ → Bool) (width : ℕ) :
    bankValue (resultAt a) width + 1 = bankValue a width + 2 ^ width * (borrowAt a width).toNat := by
  induction width with
  | zero => simp [bankValue, borrowAt]
  | succ width ih =>
      have hb := subtract_bit (borrowAt a width) (a width)
      have hbw := congrArg (fun n : ℕ => n * 2 ^ width) hb
      simp only [bankValue, Finset.sum_range_succ, borrowAt, resultAt, pow_succ] at *
      nlinarith

theorem borrowAt_false_of_pos (a : ℕ → Bool) (width : ℕ) (ha : 0 < bankValue a width) :
    borrowAt a width = false := by
  have hv := bankValue_decrement a width
  have hb := bankValue_lt (resultAt a) width
  cases h : borrowAt a width with
  | false => rfl
  | true => rw [h] at hv; simp only [Bool.toNat_true, mul_one] at hv; omega

theorem bankValue_decrement_of_pos (a : ℕ → Bool) (width : ℕ) (ha : 0 < bankValue a width) :
    bankValue (resultAt a) width = bankValue a width - 1 := by
  have hv := bankValue_decrement a width
  rw [borrowAt_false_of_pos a width ha] at hv
  simp only [Bool.toNat_false, mul_zero, add_zero] at hv
  omega

theorem nonzeroAt_iff (a : ℕ → Bool) (width : ℕ) :
    nonzeroAt a width = true ↔ 0 < bankValue (resultAt a) width := by
  induction width with
  | zero => simp [nonzeroAt, bankValue]
  | succ width ih =>
      have hp := Nat.two_pow_pos width
      have hor (z : ℕ) (bit : Bool) :
          (0 < z ∨ bit = true) ↔ 0 < z + bit.toNat * 2 ^ width := by
        cases bit <;> simp <;> omega
      have hval : bankValue (resultAt a) (width + 1) = bankValue (resultAt a) width +
          (resultAt a width).toNat * 2 ^ width := by simp only [bankValue, Finset.sum_range_succ]
      change (nonzeroAt a width || resultAt a width) = true ↔
        0 < bankValue (resultAt a) (width + 1)
      rw [Bool.or_eq_true, ih, hval]
      exact hor _ _

theorem step_tag {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (head : ℕ) (borrow nonzero : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hread : c.work head = true) :
    (machine advance).step input (cursor c head (some (tag borrow nonzero))) =
      some (cursor c (head + 1) (some (digit borrow nonzero))) := by
  have hw : Function.update c.work head true = c.work := by
    rw [← hread]; exact Function.update_eq_self _ _
  cases borrow <;> cases nonzero <;>
    simp [Machine.step, machine, tag, digit, tagInstruction, instruction, cursor,
      Move.apply, hread, hw, hi, hc]

theorem step_digit {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (head : ℕ) (borrow nonzero a : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hread : c.work head = a) :
    (machine advance).step input (cursor c head (some (digit borrow nonzero))) =
      some (cursor (writeAt c head (resultBit borrow a)) (head + 1)
        (some (skip (nextBorrow borrow a) (nonzero || resultBit borrow a)))) := by
  cases borrow <;> cases nonzero <;> cases a <;>
    simp [Machine.step, machine, digit, skip, digitInstruction, instruction, cursor,
      writeAt, Move.apply, hread, hi, hc, resultBit, nextBorrow]

theorem step_skip {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (head : ℕ) (borrow nonzero : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) :
    (machine advance).step input (cursor c head (some (skip borrow nonzero))) =
      some (cursor c (head + 1) (some (tag borrow nonzero))) := by
  cases borrow <;> cases nonzero <;>
    simp [Machine.step, machine, tag, skip, instruction, cursor, Move.apply, hi, hc,
      Function.update_eq_self]

theorem prefixWork_tag (work : ℕ → Bool) (base : ℕ) (a : ℕ → Bool) (processed i : ℕ) :
    prefixWork work base a processed (base + 6 + 3 * i) = work (base + 6 + 3 * i) := by
  simp [prefixWork, show (base + 6 + 3 * i - (base + 6)) % 3 = 0 by omega]

theorem prefixWork_a (work : ℕ → Bool) (base : ℕ) (a : ℕ → Bool) (processed i : ℕ) :
    prefixWork work base a processed (base + 6 + 3 * i + 1) =
      if i < processed then resultAt a i else work (base + 6 + 3 * i + 1) := by
  unfold prefixWork
  rw [show (base + 6 + 3 * i + 1 - (base + 6)) % 3 = 1 by omega,
    show (base + 6 + 3 * i + 1 - (base + 6)) / 3 = i by omega]
  simp [show base + 6 ≤ base + 6 + 3 * i + 1 by omega]

theorem prefixWork_b (work : ℕ → Bool) (base : ℕ) (a : ℕ → Bool) (processed i : ℕ) :
    prefixWork work base a processed (base + 6 + 3 * i + 2) = work (base + 6 + 3 * i + 2) := by
  unfold prefixWork
  rw [show (base + 6 + 3 * i + 2 - (base + 6)) % 3 = 2 by omega]
  simp

theorem prefixWork_zero (work : ℕ → Bool) (base : ℕ) (a : ℕ → Bool) :
    prefixWork work base a 0 = work := by
  funext p
  simp [prefixWork]

theorem prefixWork_succ (work : ℕ → Bool) (base : ℕ) (a : ℕ → Bool) (processed : ℕ) :
    prefixWork work base a (processed + 1) = Function.update (prefixWork work base a processed)
      (base + 6 + 3 * processed + 1) (resultAt a processed) := by
  funext p
  by_cases hp : p = base + 6 + 3 * processed + 1
  · subst p
    simp [prefixWork_a]
  · have hcond :
        (base + 6 ≤ p ∧ (p - (base + 6)) % 3 = 1 ∧ (p - (base + 6)) / 3 < processed + 1) ↔
        (base + 6 ≤ p ∧ (p - (base + 6)) % 3 = 1 ∧ (p - (base + 6)) / 3 < processed) := by
      constructor
      · rintro ⟨hr, hm, hn⟩
        refine ⟨hr, hm, ?_⟩
        have hdiv := Nat.mod_add_div (p - (base + 6)) 3
        omega
      · omega
    rw [Function.update_of_ne hp]
    simp only [prefixWork, hcond]

theorem run_column {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (head : ℕ) (borrow nonzero a : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (htag : c.work head = true)
    (ha : c.work (head + 1) = a) :
    runFrom ((machine advance).step input) (cursor c head (some (tag borrow nonzero))) 3 =
      some (cursor (writeAt c (head + 1) (resultBit borrow a)) (head + 3)
        (some (tag (nextBorrow borrow a) (nonzero || resultBit borrow a)))) := by
  have h1 := step_tag input c head borrow nonzero hi hc htag
  have h2 := step_digit input c (head + 1) borrow nonzero a hi hc ha
  have h3 := step_skip input (writeAt c (head + 1) (resultBit borrow a)) (head + 1 + 1)
    (nextBorrow borrow a) (nonzero || resultBit borrow a) hi hc
  simpa only [Nat.add_assoc] using
    (show runFrom ((machine advance).step input) (cursor c head (some (tag borrow nonzero))) 3 =
      some (cursor (writeAt c (head + 1) (resultBit borrow a)) (head + 1 + 1 + 1)
        (some (tag (nextBorrow borrow a) (nonzero || resultBit borrow a)))) by
      simp only [runFrom, Option.bind_some, h1, h2, h3])

theorem run_columns {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base width : ℕ) (a b : ℕ → Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work base width a b) :
    ∀ n ≤ width,
      runFrom ((machine advance).step input) (cursor c (base + 6) (some (tag true false))) (3 * n) =
        some (cursor {c with work := prefixWork c.work base a n} (base + 6 + 3 * n)
          (some (tag (borrowAt a n) (nonzeroAt a n)))) := by
  intro n
  induction n with
  | zero => intro _; simp [runFrom, prefixWork_zero, borrowAt, nonzeroAt]
  | succ n ih =>
      intro hn
      rw [show 3 * (n + 1) = 3 * n + 3 by omega, runFrom_add, ih (by omega), Option.bind_some]
      have htag : (prefixWork c.work base a n) (base + 6 + 3 * n) = true := by
        rw [prefixWork_tag]
        exact (hbank.2.2 n (by omega)).1
      have ha : (prefixWork c.work base a n) (base + 6 + 3 * n + 1) = a n := by
        rw [prefixWork_a, if_neg (by omega : ¬n < n)]
        exact (hbank.2.2 n (by omega)).2.1
      have hr := run_column input {c with work := prefixWork c.work base a n}
        (base + 6 + 3 * n) (borrowAt a n) (nonzeroAt a n) (a n) hi hc htag ha
      simpa [prefixWork_succ, borrowAt, nonzeroAt, resultAt, cursor, writeAt, Nat.add_mul,
        Nat.add_assoc] using hr

theorem run_entry {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base : ℕ) (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    runFrom ((machine advance).step input) (cursor c base (some (entry 0))) 6 =
      some (cursor c (base + 6) (some (tag true false))) := by
  simp [runFrom, Machine.step, machine, entry, tag, instruction, cursor, Move.apply,
    hi, hc, Function.update_eq_self, Nat.add_assoc]


end CatalyticTreeEval.Contracts.BinaryCountdown
end

/- Proof component: Solutions.CatalyticTreeEvaluation.BinaryCountdownRewind -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinaryCountdown

open CatalyticMatching.General

theorem step_rewindCursor {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (top u : ℕ) (borrow nonzero : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hu : u < top)
    (hterminal : c.work top = false)
    (htag : 0 < u → u % 3 = 0 → c.work (top - u) = true) :
    (machine advance).step input (rewindCursor c top borrow nonzero u) =
      some (rewindCursor c top borrow nonzero (u + 1)) := by
  have he : top - u - 1 = top - (u + 1) := by omega
  have hm := Nat.mod_lt u (by decide : 0 < 3)
  by_cases hz : u = 0
  · subst u
    have hw : Function.update c.work top false = c.work := by
      rw [← hterminal]; exact Function.update_eq_self _ _
    cases borrow <;> cases nonzero <;>
      simp [Machine.step, machine, instruction, tagInstruction, tag, rewind, rewindInstruction,
        rewindCursor, cursor, Move.apply, hi, hc, hterminal, hw]
  · have hpos : 0 < u := by omega
    have hcases : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases hcases with h | h | h
    · have hs : (u + 1) % 3 = 1 := by omega
      have hread := htag hpos h
      have hw : Function.update c.work (top - u) true = c.work := by
        rw [← hread]; exact Function.update_eq_self _ _
      cases nonzero <;>
        simp [Machine.step, machine, instruction, rewind, rewindInstruction, rewindCursor,
          cursor, Move.apply, hi, hc, hz, h, hs, he, hread, hw]
    · have hs : (u + 1) % 3 = 2 := by omega
      cases nonzero <;>
        simp [Machine.step, machine, instruction, rewind, rewindInstruction, rewindCursor,
          cursor, Move.apply, hi, hc, hz, h, hs, he, Function.update_eq_self]
    · have hs : (u + 1) % 3 = 0 := by omega
      cases nonzero <;>
        simp [Machine.step, machine, instruction, rewind, rewindInstruction, rewindCursor,
          cursor, Move.apply, hi, hc, hz, h, hs, he, Function.update_eq_self]

theorem run_rewind_left {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base width : ℕ) (borrow nonzero : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hterminal : c.work (base + 6 + 3 * width) = false)
    (htags : ∀ i < width, c.work (base + 6 + 3 * i) = true) :
    ∀ u ≤ 3 * width + 3,
      runFrom ((machine advance).step input) (rewindCursor c (base + 6 + 3 * width) borrow nonzero 0) u =
        some (rewindCursor c (base + 6 + 3 * width) borrow nonzero u) := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
      intro hu
      rw [runFrom_succ, ih (by omega), Option.bind_some]
      apply step_rewindCursor input c _ u borrow nonzero hi hc (by omega) hterminal
      intro hup hum
      have he := Nat.mod_add_div u 3
      have hk : 0 < u / 3 ∧ u / 3 ≤ width := by omega
      have hidx : width - u / 3 < width := by omega
      have hhead : base + 6 + 3 * width - u = base + 6 + 3 * (width - u / 3) := by omega
      rw [hhead]
      exact htags _ hidx

theorem run_exit {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base : ℕ) (nonzero : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead + advance.toNat ≤ c.catalyst.length)
    (hmarker : c.work (base + 3) = false) :
    ∀ u ≤ 4,
      runFrom ((machine advance).step input) (exitCursor c base nonzero 0) u =
        some (exitCursor c base nonzero u) := by
  have hc0 : c.catalystHead ≤ c.catalyst.length := by omega
  have hw : Function.update c.work (base + 3) false = c.work := by
    rw [← hmarker]; exact Function.update_eq_self _ _
  intro u hu
  have hcases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;> cases advance <;> cases nonzero <;>
    simp [runFrom, Machine.step, machine, instruction, rewind, rewindInstruction, back,
      backInstruction, writeFlag, exitCursor, Move.apply, hi, hc, hc0, hmarker, hw,
      Function.update_eq_self] <;> (simp only [Bool.toNat_true] at hc; omega)

theorem rewind_exit_seam {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (borrow nonzero : Bool) :
    rewindCursor c (base + 6 + 3 * width) borrow nonzero (3 * width + 3) =
      exitCursor c base nonzero 0 := by
  have hh : base + 6 + 3 * width - (3 * width + 3) = base + 3 := by omega
  simp [rewindCursor, exitCursor, cursor, hh] <;> rfl

theorem run_rewind {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base width : ℕ) (borrow nonzero : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead + advance.toNat ≤ c.catalyst.length)
    (hterminal : c.work (base + 6 + 3 * width) = false)
    (hmarker : c.work (base + 3) = false)
    (htags : ∀ i < width, c.work (base + 6 + 3 * i) = true) :
    runFrom ((machine advance).step input) (rewindCursor c (base + 6 + 3 * width) borrow nonzero 0)
      (3 * width + 7) = some (exitCursor c base nonzero 4) := by
  rw [show 3 * width + 7 = (3 * width + 3) + 4 by omega, runFrom_add,
    run_rewind_left input c base width borrow nonzero hi (by omega) hterminal htags _ le_rfl,
    Option.bind_some, rewind_exit_seam]
  exact run_exit input c base nonzero hi hc hmarker _ le_rfl

theorem prefixWork_marker (work : ℕ → Bool) (base : ℕ) (a : ℕ → Bool) (n : ℕ) :
    prefixWork work base a n (base + 3) = work (base + 3) := by
  unfold prefixWork
  rw [if_neg (by omega)]

/-- Exact native countdown/seek run, before attaching the trajectory frame. -/
theorem run_bank {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base width : ℕ) (a b : ℕ → Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead + advance.toNat ≤ c.catalyst.length)
    (hbank : bankContents c.work base width a b) :
    runFrom ((machine advance).step input) (cursor c base (some (entry 0))) (6 * width + 13) =
      some (finished c base width a) := by
  have hc0 : c.catalystHead ≤ c.catalyst.length := by omega
  rw [show 6 * width + 13 = 6 + (3 * width + (3 * width + 7)) by omega,
    runFrom_add, run_entry input c base hi hc0, Option.bind_some,
    runFrom_add, run_columns input c base width a b hi hc0 hbank _ le_rfl, Option.bind_some]
  let C : Config (machine advance) := {c with work := prefixWork c.work base a width}
  have ht : C.work (base + 6 + 3 * width) = false := by
    simpa only [C, prefixWork_tag] using hbank.2.1
  have hm : C.work (base + 3) = false := by
    simpa only [C, prefixWork_marker] using hbank.1
  have htags : ∀ i < width, C.work (base + 6 + 3 * i) = true := by
    intro i hi
    simpa only [C, prefixWork_tag] using (hbank.2.2 i hi).1
  have hr := run_rewind input C base width (borrowAt a width) (nonzeroAt a width) hi hc ht hm htags
  simpa [rewindCursor, cursor, C, exitCursor, finished] using hr

theorem finished_flag {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) :
    (finished c base width a).work base = nonzeroAt a width := by simp [finished]

theorem finished_a {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) (i : ℕ) (hi : i < width) :
    (finished c base width a).work (base + 6 + 3 * i + 1) = resultAt a i := by
  have hn : base + 6 + 3 * i + 1 ≠ base := by omega
  simp [finished, hn, prefixWork_a, hi]

theorem finished_b {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) (i : ℕ) :
    (finished c base width a).work (base + 6 + 3 * i + 2) = c.work (base + 6 + 3 * i + 2) := by
  have hn : base + 6 + 3 * i + 2 ≠ base := by omega
  simp [finished, hn, prefixWork_b]

theorem finished_savedPrefix {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) : SavedPrefix base c (finished c base width a) := by
  intro p hp
  have hn : p ≠ base := by omega
  simp only [finished, Function.update_of_ne hn, prefixWork]
  rw [if_neg (by omega)]


end CatalyticTreeEval.Contracts.BinaryCountdown
end

/- Proof component: Solutions.CatalyticTreeEvaluation.BinaryCountdownTrace -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinaryCountdown

open CatalyticMatching.General

theorem run_entry_prefix {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base : ℕ) (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (u : ℕ) (hu : u ≤ 6) :
    runFrom ((machine advance).step input) (cursor c base (some (entry 0))) u =
      some (entryCursor c base u) := by
  interval_cases u <;>
    simp [entryCursor, runFrom, Machine.step, machine, entry, tag, instruction, cursor,
      Move.apply, hi, hc, Function.update_eq_self, Nat.add_assoc]

theorem run_column_prefix {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base width : ℕ) (a b : ℕ → Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work base width a b)
    (n p : ℕ) (hn : n < width) (hp : p < 3) :
    runFrom ((machine advance).step input)
      (cursor {c with work := prefixWork c.work base a n} (base + 6 + 3 * n)
        (some (tag (borrowAt a n) (nonzeroAt a n)))) p = some (columnCursor c base a n p) := by
  let C : Config (machine advance) := {c with work := prefixWork c.work base a n}
  have htag : C.work (base + 6 + 3 * n) = true := by
    simpa only [C, prefixWork_tag] using (hbank.2.2 n hn).1
  have ha : C.work (base + 6 + 3 * n + 1) = a n := by
    rw [show C.work = prefixWork c.work base a n from rfl, prefixWork_a, if_neg (by omega)]
    exact (hbank.2.2 n hn).2.1
  have h1 := step_tag input C (base + 6 + 3 * n) (borrowAt a n) (nonzeroAt a n) hi hc htag
  have h2 := step_digit input C (base + 6 + 3 * n + 1)
    (borrowAt a n) (nonzeroAt a n) (a n) hi hc ha
  have hcases : p = 0 ∨ p = 1 ∨ p = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · rfl
  · simpa [columnCursor, C] using h1
  · simpa [runFrom, h1, h2, columnCursor, C, cursor, writeAt, prefixWork_succ,
      borrowAt, nonzeroAt, resultAt, Nat.add_assoc] using
      (show runFrom ((machine advance).step input)
        (cursor C (base + 6 + 3 * n) (some (tag (borrowAt a n) (nonzeroAt a n)))) 2 =
        some (cursor (writeAt C (base + 6 + 3 * n + 1) (resultBit (borrowAt a n) (a n)))
          (base + 6 + 3 * n + 1 + 1)
          (some (skip (nextBorrow (borrowAt a n) (a n))
            (nonzeroAt a n || resultBit (borrowAt a n) (a n))))) by
        simp only [runFrom, Option.bind_some, h1, h2])

theorem run_forward_prefix {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base width : ℕ) (a b : ℕ → Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead ≤ c.catalyst.length) (hbank : bankContents c.work base width a b)
    (u : ℕ) (hu : u ≤ 3 * width) :
    runFrom ((machine advance).step input) (cursor c (base + 6) (some (tag true false))) u =
      some (forwardCursor c base a u) := by
  have hn : u / 3 ≤ width := by omega
  have hp : u % 3 < 3 := Nat.mod_lt _ (by decide)
  have he : u = 3 * (u / 3) + u % 3 := by omega
  by_cases hzero : u % 3 = 0
  · rw [show u = 3 * (u / 3) by omega, run_columns input c base width a b hi hc hbank _ hn]
    simp [forwardCursor, columnCursor, show (3 * (u / 3)) / 3 = u / 3 by omega,
      show (3 * (u / 3)) % 3 = 0 by omega]
  · have hlt : u / 3 < width := by omega
    rw [he, runFrom_add, run_columns input c base width a b hi hc hbank _ hn, Option.bind_some]
    have hr := run_column_prefix input c base width a b hi hc hbank (u / 3) (u % 3) hlt hp
    simpa only [forwardCursor, show (3 * (u / 3) + u % 3) / 3 = u / 3 by omega,
      show (3 * (u / 3) + u % 3) % 3 = u % 3 by omega] using hr

end CatalyticTreeEval.Contracts.BinaryCountdown
end

/- Proof component: Solutions.CatalyticTreeEvaluation.BinaryCountdownContract -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinaryCountdown

open CatalyticMatching.General

theorem run_rewind_prefix {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base width : ℕ) (borrow nonzero : Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead + advance.toNat ≤ c.catalyst.length)
    (hterminal : c.work (base + 6 + 3 * width) = false) (hmarker : c.work (base + 3) = false)
    (htags : ∀ i < width, c.work (base + 6 + 3 * i) = true) (u : ℕ) (hu : u ≤ 3 * width + 7) :
    runFrom ((machine advance).step input)
      (rewindCursor c (base + 6 + 3 * width) borrow nonzero 0) u =
      some (if u ≤ 3 * width + 3 then rewindCursor c (base + 6 + 3 * width) borrow nonzero u
        else exitCursor c base nonzero (u - (3 * width + 3))) := by
  by_cases h : u ≤ 3 * width + 3
  · simpa only [if_pos h] using
      run_rewind_left input c base width borrow nonzero hi (by omega) hterminal htags u h
  · rw [if_neg h]
    have he : u = (3 * width + 3) + (u - (3 * width + 3)) := by omega
    rw [he, runFrom_add,
      run_rewind_left input c base width borrow nonzero hi (by omega) hterminal htags _ le_rfl,
      Option.bind_some, rewind_exit_seam]
    have hrem : u - (3 * width + 3) ≤ 4 := by omega
    simpa only [Nat.add_sub_cancel_left] using run_exit input c base nonzero hi hc hmarker _ hrem

theorem run_bank_prefix {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base width : ℕ) (a b : ℕ → Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead + advance.toNat ≤ c.catalyst.length)
    (hbank : bankContents c.work base width a b) (u : ℕ) (hu : u ≤ 6 * width + 13) :
    runFrom ((machine advance).step input) (cursor c base (some (entry 0))) u =
      some (bankCursor c base width a u) := by
  have hc0 : c.catalystHead ≤ c.catalyst.length := by omega
  unfold bankCursor
  by_cases he : u ≤ 6
  · rw [if_pos he]
    exact run_entry_prefix input c base hi hc0 u he
  · rw [if_neg he]
    by_cases hf : u ≤ 6 + 3 * width
    · rw [if_pos hf, show u = 6 + (u - 6) by omega, runFrom_add,
        run_entry input c base hi hc0, Option.bind_some]
      simpa only [Nat.add_sub_cancel_left] using
        run_forward_prefix input c base width a b hi hc0 hbank (u - 6) (by omega)
    · rw [if_neg hf, show u = 6 + (3 * width + (u - (6 + 3 * width))) by omega,
        runFrom_add, run_entry input c base hi hc0, Option.bind_some,
        runFrom_add, run_columns input c base width a b hi hc0 hbank _ le_rfl, Option.bind_some]
      let C : Config (machine advance) := {c with work := prefixWork c.work base a width}
      have ht : C.work (base + 6 + 3 * width) = false := by
        simpa only [C, prefixWork_tag] using hbank.2.1
      have hm : C.work (base + 3) = false := by
        simpa only [C, prefixWork_marker] using hbank.1
      have htags : ∀ i < width, C.work (base + 6 + 3 * i) = true := by
        intro i hi
        simpa only [C, prefixWork_tag] using (hbank.2.2 i hi).1
      have hr := run_rewind_prefix input C base width (borrowAt a width) (nonzeroAt a width)
        hi hc ht hm htags (u - (6 + 3 * width)) (by omega)
      simpa [rewindCursor, cursor, C,
        show 6 + (3 * width + (u - (6 + 3 * width))) - (6 + 3 * width) =
          u - (6 + 3 * width) by omega] using hr

theorem prefixWork_outside (work : ℕ → Bool) (base width processed : ℕ) (a : ℕ → Bool)
    (hn : processed ≤ width) (p : ℕ) (hp : p ∉ (footprint base width).work) :
    prefixWork work base a processed p = work p := by
  unfold prefixWork
  split_ifs with h
  · exfalso
    apply hp
    right
    refine ⟨(p - (base + 6)) / 3, lt_of_lt_of_le h.2.2 hn, ?_⟩
    have he := Nat.mod_add_div (p - (base + 6)) 3
    omega
  · rfl

private theorem frame_prefix {advance : Bool} (c : Config (machine advance))
    (base width processed head : ℕ) (a : ℕ → Bool) (q : Option (Fin 30))
    (hn : processed ≤ width) (hlo : base ≤ head) (hhi : head ≤ base + 6 + 3 * width) :
    (envelope c base width).Contains
      (cursor {c with work := prefixWork c.work base a processed} head q) ∧
    SameOutside (footprint base width) c
      (cursor {c with work := prefixWork c.work base a processed} head q) := by
  constructor
  · simp only [envelope, Envelope.Contains, cursor]
    omega
  · exact ⟨fun p hp => prefixWork_outside c.work base width processed a hn p hp,
      rfl, fun _ _ => rfl⟩

private theorem frame_entry {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) (u : ℕ) (hu : u ≤ 6) :
    (envelope c base width).Contains (entryCursor c base u) ∧
      SameOutside (footprint base width) c (entryCursor c base u) := by
  unfold entryCursor
  split_ifs with h
  · simpa [prefixWork_zero, cursor] using
      frame_prefix c base width 0 (base + u) a (some (entry ⟨u, h⟩)) (by omega) (by omega) (by omega)
  · simpa [prefixWork_zero, cursor] using
      frame_prefix c base width 0 (base + 6) a (some (tag true false)) (by omega) (by omega) (by omega)

private theorem frame_forward {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) (u : ℕ) (hu : u ≤ 3 * width) :
    (envelope c base width).Contains (forwardCursor c base a u) ∧
      SameOutside (footprint base width) c (forwardCursor c base a u) := by
  have he := Nat.mod_add_div u 3
  have hp := Nat.mod_lt u (by decide : 0 < 3)
  unfold forwardCursor columnCursor
  split_ifs with h0 h1
  · apply frame_prefix <;> omega
  · apply frame_prefix <;> omega
  · apply frame_prefix <;> omega

private theorem frame_finished {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) :
    (envelope c base width).Contains (finished c base width a) ∧
      SameOutside (footprint base width) c (finished c base width a) := by
  constructor
  · simp [envelope, Envelope.Contains, finished] <;> omega
  · refine ⟨?_, rfl, fun _ _ => rfl⟩
    intro p hp
    have hn : p ≠ base := by intro h; apply hp; exact Or.inl h
    simp only [finished, Function.update_of_ne hn]
    exact prefixWork_outside c.work base width width a le_rfl p hp

private theorem frame_exit {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) (u : ℕ) (hu : u ≤ 4) :
    (envelope c base width).Contains
      (exitCursor {c with work := prefixWork c.work base a width} base (nonzeroAt a width) u) ∧
    SameOutside (footprint base width) c
      (exitCursor {c with work := prefixWork c.work base a width} base (nonzeroAt a width) u) := by
  by_cases h : u ≤ 3
  · let q : Option (Fin 30) := if u = 0 then some (rewind (nonzeroAt a width) 0)
        else if u = 1 then some (back (nonzeroAt a width) 0)
        else if u = 2 then some (back (nonzeroAt a width) 1)
        else if u = 3 then some (writeFlag (nonzeroAt a width)) else none
    have hr := frame_prefix c base width width (base + 3 - u) a q le_rfl (by omega) (by omega)
    have hcursor : exitCursor {c with work := prefixWork c.work base a width}
        base (nonzeroAt a width) u =
        cursor {c with work := prefixWork c.work base a width} (base + 3 - u) q := by
      simp only [exitCursor, cursor, if_pos h, min_eq_left h, q]
      rfl
    rw [hcursor]
    exact hr
  · have he : u = 4 := by omega
    subst u
    simpa [exitCursor, finished] using frame_finished c base width a

theorem bankCursor_frame {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) (u : ℕ) (hu : u ≤ 6 * width + 13) :
    (envelope c base width).Contains (bankCursor c base width a u) ∧
      SameOutside (footprint base width) c (bankCursor c base width a u) := by
  dsimp only [bankCursor]
  split_ifs with he hf hr
  · exact frame_entry c base width a u he
  · exact frame_forward c base width a (u - 6) (by omega)
  · unfold rewindCursor
    apply frame_prefix <;> omega
  · exact frame_exit c base width a (u - (6 + 3 * width) - (3 * width + 3)) (by omega)

theorem bankCursor_live {advance : Bool} (c : Config (machine advance))
    (base width : ℕ) (a : ℕ → Bool) (u : ℕ) (hu : u < 6 * width + 13) :
    (bankCursor c base width a u).state ≠ none := by
  dsimp only [bankCursor]
  split_ifs with he hf hr
  · unfold entryCursor
    split_ifs <;> simp only [cursor] <;> (intro h; cases h)
  · unfold forwardCursor columnCursor
    split_ifs <;> simp only [cursor] <;> (intro h; cases h)
  · simp only [rewindCursor, cursor]
    intro h
    cases h
  · have hrem : u - (6 + 3 * width) - (3 * width + 3) < 4 := by omega
    have hcases : u - (6 + 3 * width) - (3 * width + 3) = 0 ∨
        u - (6 + 3 * width) - (3 * width + 3) = 1 ∨
        u - (6 + 3 * width) - (3 * width + 3) = 2 ∨
        u - (6 + 3 * width) - (3 * width + 3) = 3 := by omega
    rcases hcases with h | h | h | h <;> simp [exitCursor, h] <;> (intro h; cases h)

/-- Full exact native leaf: all transitions, all addressed heads, and every
untouched work/catalyst cell are certified. Saved caller prefixes and B slots
are outside the writable footprint. -/
theorem bank_firstExit {advance : Bool} (input : List Bool) (c : Config (machine advance))
    (base width : ℕ) (a b : ℕ → Bool) (hi : c.inputHead ≤ input.length + 1)
    (hc : c.catalystHead + advance.toNat ≤ c.catalyst.length)
    (hbank : bankContents c.work base width a b) :
    FirstExit ((machine advance).step input)
      (fun _ d => (envelope c base width).Contains d ∧ SameOutside (footprint base width) c d)
      {d | d.state = none} (cursor c base (some (entry 0)))
      (finished c base width a) (6 * width + 13) where
  result := run_bank input c base width a b hi hc hbank
  during u hu d hd := by
    rw [run_bank_prefix input c base width a b hi hc hbank u hu] at hd
    cases Option.some.inj hd
    exact bankCursor_frame c base width a u hu
  exit_mem := rfl
  cut u hu d hd := by
    rw [run_bank_prefix input c base width a b hi hc hbank u (by omega)] at hd
    cases Option.some.inj hd
    exact bankCursor_live c base width a u hu


end CatalyticTreeEval.Contracts.BinaryCountdown
end

/- Proof component: Solutions.CatalyticTreeEvaluation.BinarySeek -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.BinarySeek

open CatalyticMatching.General
open BinaryCountdown

theorem phase_workHead {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a : ℕ → Bool) (n : ℕ) : (phase c base width a n).workHead = base := by
  cases n <;> rfl

theorem phase_inputHead {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a : ℕ → Bool) (n : ℕ) : (phase c base width a n).inputHead = c.inputHead := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem phase_catalyst {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a : ℕ → Bool) (n : ℕ) :
    (phase c base width a n).catalyst = c.catalyst := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem phase_output {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a : ℕ → Bool) (n : ℕ) : (phase c base width a n).output = c.output := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem phase_catalystHead {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a : ℕ → Bool) (n : ℕ) :
    (phase c base width a n).catalystHead = c.catalystHead + n * advance.toNat := by
  induction n with
  | zero => simp [phase, cursor]
  | succ n ih =>
      change (phase c base width a n).catalystHead + advance.toNat = _
      rw [ih]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

theorem phase_savedPrefix {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a : ℕ → Bool) (n : ℕ) : SavedPrefix base c (phase c base width a n) := by
  induction n with
  | zero => intro p hp; rfl
  | succ n ih =>
      intro p hp
      exact (finished_savedPrefix (phase c base width a n) base width (digitsAt a n) p hp).trans (ih p hp)

theorem phase_b {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a : ℕ → Bool) (n i : ℕ) :
    (phase c base width a n).work (base + 6 + 3 * i + 2) = c.work (base + 6 + 3 * i + 2) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (finished_b _ base width _ i).trans ih

theorem phase_bank {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a b : ℕ → Bool) (hbank : bankContents c.work base width a b) (n : ℕ) :
    bankContents (phase c base width a n).work base width (digitsAt a n) b := by
  induction n with
  | zero => exact hbank
  | succ n ih =>
      refine ⟨?_, ?_, ?_⟩
      · have hn : base + 3 ≠ base := by omega
        simpa only [phase, finished, Function.update_of_ne hn, prefixWork_marker] using ih.1
      · have hn : base + 6 + 3 * width ≠ base := by omega
        simpa only [phase, finished, Function.update_of_ne hn, prefixWork_tag] using ih.2.1
      · intro i hi
        refine ⟨?_, ?_, ?_⟩
        · have hn : base + 6 + 3 * i ≠ base := by omega
          simpa only [phase, finished, Function.update_of_ne hn, prefixWork_tag] using (ih.2.2 i hi).1
        · exact finished_a _ base width _ i hi
        · exact (finished_b _ base width _ i).trans (ih.2.2 i hi).2.2

theorem digitsAt_value (a : ℕ → Bool) (width n : ℕ) (hn : n ≤ bankValue a width) :
    bankValue (digitsAt a n) width = bankValue a width - n := by
  induction n with
  | zero => simp [digitsAt]
  | succ n ih =>
      have hn' : n ≤ bankValue a width := by omega
      have hv := ih hn'
      have hpos : 0 < bankValue (digitsAt a n) width := by omega
      rw [digitsAt, bankValue_decrement_of_pos _ width hpos, hv]
      omega

theorem phase_flag {advance : Bool} (c : Config (BinaryCountdown.machine advance))
    (base width : ℕ) (a : ℕ → Bool)
    (hflag : c.work base = decide (0 < bankValue a width)) (n : ℕ) :
    (phase c base width a n).work base = decide (0 < bankValue (digitsAt a n) width) := by
  cases n with
  | zero => exact hflag
  | succ n =>
      rw [phase, finished_flag]
      change nonzeroAt (digitsAt a n) width = decide (0 < bankValue (resultAt (digitsAt a n)) width)
      exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq, nonzeroAt_iff])

end CatalyticTreeEval.Contracts.BinarySeek
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeMSBCounterPort -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.NativeMSBFold

open NativeRoundSupport
open RestoringRound (SameIO)

theorem counter_exec {N : Main.Machine} {lanes : ℕ} (lane : Fin lanes)
    (input : List Bool) (c : Config N) (base width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length)
    (origin : WorkLanes.OriginTrack lanes base c.work) (hhead : c.workHead = base + lane.val)
    (hmarker : c.work (WorkLanes.address lane base 3) = false)
    (hbank : laneBank lane base width c.work a b) :
    ∃ d : Config (WorkLanes.machine (BinaryCountdown.machine false) lanes lane),
      FirstExit ((WorkLanes.machine (BinaryCountdown.machine false) lanes lane).step input)
        (fun _ e => e.workHead < base + (lanes + 1) * (7 + 3 * width) ∧
          Frame (WorkLanes.liftedFootprint lane base ⟨Set.Ico 0 (7 + 3 * width),∅⟩) c e)
        {e | e.state = none} (startOn (WorkLanes.machine (BinaryCountdown.machine false) lanes lane) c) d
        ((6 * width + 13) * WorkLanes.macroTime lane) ∧
      d.workHead = base + lane.val ∧ WorkLanes.OriginTrack lanes base d.work ∧
      WorkLanes.Inactive lane base c.work d.work ∧
      d.work (WorkLanes.address lane base 0) = decide (0 < BinaryCountdown.bankValue (BinaryCountdown.resultAt a) width) ∧
      laneBank lane base width d.work (BinaryCountdown.resultAt a) b ∧
      d.work (WorkLanes.address lane base 3) = false ∧ SameIO c d := by
  let A := BinaryCountdown.machine false
  let s := logicalStart A lane base c
  let target := BinaryCountdown.finished s 0 width a
  have hSbank : BinaryCountdown.bankContents s.work 0 width a b := ⟨hmarker,hbank.1,hbank.2⟩
  have HS0 := BinaryCountdown.bank_firstExit (advance := false) input s 0 width a b hi hc hSbank
  have HS : FirstExit (A.step input)
      (fun _ e => (BinaryCountdown.envelope s 0 width).Contains e ∧
        SameOutside (BinaryCountdown.footprint 0 width) s e)
      {e | e.state = none} s target (6 * width + 13) := by
    simpa only [show BinaryCountdown.cursor s 0 (some (BinaryCountdown.entry 0)) = s from rfl] using HS0
  have Hsource : FirstExit (A.step input)
      (fun _ e => e.workHead < 7 + 3 * width ∧ Frame ⟨Set.Ico 0 (7 + 3 * width),∅⟩ s e)
      {e | e.state = none} s target (6 * width + 13) := by
    refine { result := HS.result, exit_mem := HS.exit_mem, cut := HS.cut, during := ?_ }
    intro u hu e he
    have HF := HS.during u hu e he
    refine ⟨?_,?_⟩
    · have H := HF.1.2.1
      dsimp [BinaryCountdown.envelope] at H
      omega
    · apply (show Frame (BinaryCountdown.footprint 0 width) s e from HF.2).mono
      · intro p hp
        rcases hp with hp|⟨i,hiw,hp⟩ <;> subst p <;> constructor <;> omega
      · exact Set.Subset.refl _
  have htbank : BinaryCountdown.bankContents target.work 0 width (BinaryCountdown.resultAt a) b := by
    have H := BinarySeek.phase_bank s 0 width a b hSbank 1
    simpa [target,BinarySeek.phase,BinarySeek.digitsAt,BinaryCountdown.cursor,BinaryCountdown.finished] using H
  have htflag : target.work 0 = decide (0 < BinaryCountdown.bankValue (BinaryCountdown.resultAt a) width) := by
    change BinaryCountdown.nonzeroAt a width = decide (0 < BinaryCountdown.bankValue (BinaryCountdown.resultAt a) width)
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq,BinaryCountdown.nonzeroAt_iff])
  have htIO : SameIO s target := ⟨rfl,rfl,rfl,rfl⟩
  obtain ⟨updated,horigin,hmatches,hinactive,Hnative⟩ := lift_port A lane input c base target (6 * width + 13)
    (7 + 3 * width) ⟨Set.Ico 0 (7 + 3 * width),∅⟩ hi hc origin hhead Hsource
  let d := WorkLanes.embed A lanes lane base target updated
  have hwork : (fun p => updated (WorkLanes.address lane base p)) = target.work := funext hmatches
  refine ⟨d,Hnative,?_,horigin,hinactive,?_,?_,?_,embed_sameIO A lane base c target updated htIO⟩
  · simp [d,target,WorkLanes.embed,WorkLanes.snapshot,BinaryCountdown.finished,WorkLanes.address]
  · exact (hmatches 0).trans htflag
  · change ShiftAppend.bankContents (fun p => updated (WorkLanes.address lane base p)) 6 width (BinaryCountdown.resultAt a) b
    rw [hwork]
    exact ⟨htbank.2.1,htbank.2.2⟩
  · exact (hmatches 3).trans htbank.1

end CatalyticTreeEval.Contracts.NativeMSBFold
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBankAllocateBody -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace CatalyticTreeEval.Contracts.NativeBankAllocate

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

/-- One initialized column followed by the actual binary countdown. The
counter's width is independent of the number of columns being allocated. -/
theorem body_exec {N : Main.Machine} {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : bookmark ∉ selected)
    (notCounter : counter ∉ selected) (distinct : counter ≠ bookmark)
    (input : List Bool) (c : Config N) (base row counterWidth : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = WorkLanes.address counter base 0)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (unique : ∀ p, c.work (WorkLanes.address bookmark base p) = decide (p = row))
    (marker : c.work (WorkLanes.address counter base 3) = false)
    (bank : NativeMSBFold.laneBank counter base counterWidth c.work a b) :
    ∃ d : Config (body counter bookmark selected),
      FirstExit ((body counter bookmark selected).step input)
        (fun _ e => e.workHead < base+(lanes+1)*max (row+4) (7+3*counterWidth) ∧
          Frame ((advanceFootprint lanes base row).union
            (WorkLanes.liftedFootprint counter base ⟨Set.Ico 0 (7+3*counterWidth),∅⟩)) c e)
        {e | e.state=none} (startOn (body counter bookmark selected) c) d
        (advanceTime counter bookmark row+(6*counterWidth+13)*WorkLanes.macroTime counter) ∧
      d.workHead = WorkLanes.address counter base 0 ∧
      WorkLanes.OriginTrack lanes base d.work ∧
      (∀ p, d.work (WorkLanes.address bookmark base p) = decide (p = row+3)) ∧
      d.work (WorkLanes.address counter base 0) =
        decide (0 < BinaryCountdown.bankValue (BinaryCountdown.resultAt a) counterWidth) ∧
      NativeMSBFold.laneBank counter base counterWidth d.work (BinaryCountdown.resultAt a) b ∧
      d.work (WorkLanes.address counter base 3) = false ∧
      (∀ other : Fin lanes, other ≠ counter → ∀ p,
        d.work (WorkLanes.address other base p) =
          advanceWork bookmark selected base row c.work (WorkLanes.address other base p)) ∧
      SameIO c d := by
  let A := advance counter bookmark selected
  let B := WorkLanes.machine (BinaryCountdown.machine false) lanes counter
  let bound := base+(lanes+1)*max (row+4) (7+3*counterWidth)
  let F := (advanceFootprint lanes base row).union
    (WorkLanes.liftedFootprint counter base ⟨Set.Ico 0 (7+3*counterWidth),∅⟩)
  obtain ⟨da,HA,hah,haw,hao,hab,haIO⟩ := advance_exec counter bookmark selected notSelected
    input c base row hi hc hhead origin unique
  have retained (p : ℕ) : da.work (WorkLanes.address counter base p) =
      c.work (WorkLanes.address counter base p) := by
    rw [haw]
    exact advance_inactive bookmark counter selected notCounter distinct base row c.work p
  have hia : da.inputHead ≤ input.length+1 := by rw [haIO.1]; exact hi
  have hca : da.catalystHead ≤ da.catalyst.length := by rw [haIO.2.1,haIO.2.2.1]; exact hc
  have markerA : da.work (WorkLanes.address counter base 3) = false := (retained 3).trans marker
  have bankA : NativeMSBFold.laneBank counter base counterWidth da.work a b := by
    change ShiftAppend.bankContents (fun p => da.work (WorkLanes.address counter base p)) 6 counterWidth a b
    have he : (fun p => da.work (WorkLanes.address counter base p)) =
        (fun p => c.work (WorkLanes.address counter base p)) := funext retained
    rw [he]
    exact bank
  obtain ⟨dc,HC,hch,hco,hci,hcf,hcb,hcm,hcIO⟩ := NativeMSBFold.counter_exec counter input da base counterWidth
    a b hia hca hao (by simpa [WorkLanes.address] using hah) markerA bankA
  have HAf := firstExit_mono input c _ _ _ _ bound _ F HA
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (le_max_left _ _)) _)
    (by intro p hp; exact Or.inl hp) (by intro p hp; exact Or.inl hp)
  have HCf := firstExit_mono input da _ _ _ _ bound _ F HC
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (le_max_right _ _)) _)
    (by intro p hp; exact Or.inr hp) (by intro p hp; exact Or.inr hp)
  have H := framed_seq A B input c da dc (advanceTime counter bookmark row)
    ((6*counterWidth+13)*WorkLanes.macroTime counter) bound F HAf HCf
  let d := Sequential.rightConfig A B dc
  have other (lane : Fin lanes) (hne : lane ≠ counter) (p : ℕ) :
      d.work (WorkLanes.address lane base p) =
        advanceWork bookmark selected base row c.work (WorkLanes.address lane base p) := by
    change dc.work _ = _
    rw [NativeMSBFold.inactive_other_lane counter lane base da.work dc.work hci hne p,haw]
  refine ⟨d,H,?_,hco,?_,hcf,hcb,hcm,other,sameIO_trans haIO hcIO⟩
  · change dc.workHead = WorkLanes.address counter base 0
    simpa only [WorkLanes.address,Nat.mul_zero,Nat.add_zero] using hch
  · intro p
    rw [other bookmark distinct.symm p]
    exact advance_bookmark bookmark selected notSelected base row c.work unique p

end CatalyticTreeEval.Contracts.NativeBankAllocate
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeFiniteIteration -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeFiniteIteration

universe u

/-- Choose a finite trajectory from proved native body contracts. This is a
proof witness only: no choice or trajectory is supplied to a transition table. -/
theorem exists_phases {C : Type u} (P : ℕ → C → Prop) (R : ℕ → C → C → Prop)
    (initial : C) (start : P 0 initial) (limit : ℕ)
    (next : ∀ n < limit, ∀ c, P n c → ∃ d, P (n+1) d ∧ R n c d) :
    ∃ phase : ℕ → C, phase 0 = initial ∧
      (∀ n ≤ limit, P n (phase n)) ∧ (∀ n < limit, R n (phase n) (phase (n+1))) := by
  classical
  revert next
  induction limit with
  | zero =>
    intro _
    refine ⟨fun _ => initial,rfl,?_,?_⟩
    · intro n hn
      have : n=0 := by omega
      subst n
      exact start
    · intro n hn
      omega
  | succ limit ih =>
    intro next
    obtain ⟨phase,h0,hP,hR⟩ := ih (fun n hn c hc => next n (by omega) c hc)
    obtain ⟨d,hd,hstep⟩ := next limit (by omega) (phase limit) (hP limit le_rfl)
    refine ⟨Function.update phase (limit+1) d,?_,?_,?_⟩
    · rw [Function.update_of_ne (by omega : (0:ℕ) ≠ limit+1)]
      exact h0
    · intro n hn
      by_cases last : n=limit+1
      · subst n
        simpa only [Function.update_self] using hd
      · rw [Function.update_of_ne last]
        exact hP n (by omega)
    · intro n hn
      by_cases last : n=limit
      · subst n
        rw [Function.update_of_ne (by omega : limit ≠ limit+1),Function.update_self]
        exact hstep
      · rw [Function.update_of_ne (by omega : n ≠ limit+1),
          Function.update_of_ne (by omega : n+1 ≠ limit+1)]
        exact hR n (by omega)

end CatalyticTreeEval.Contracts.NativeFiniteIteration
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBankAllocateLoop -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace CatalyticTreeEval.Contracts.NativeBankAllocate

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

/-- The complete addressed physical prefix, including the actual counter bank. -/
def allocationBound (lanes base counterWidth count : ℕ) : ℕ :=
  base+(lanes+1)*(7+3*max count counterWidth)

def allocationFootprint (lanes base counterWidth count : ℕ) : Footprint :=
  ⟨Set.Ico base (allocationBound lanes base counterWidth count),∅⟩

def iterationTime {lanes : ℕ} (counter bookmark : Fin lanes) (counterWidth n : ℕ) : ℕ :=
  advanceTime counter bookmark (6+3*n)+(6*counterWidth+13)*WorkLanes.macroTime counter

/-- Semantic bookkeeping for the proved trajectory. It is not runtime storage. -/
structure Progress {N : Main.Machine} {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (base counterWidth : ℕ) (a b : ℕ → Bool)
    (initial : Config N) (n : ℕ) (c : Config (body counter bookmark selected)) : Prop where
  head : c.workHead=WorkLanes.address counter base 0
  origin : WorkLanes.OriginTrack lanes base c.work
  book : ∀ p, c.work (WorkLanes.address bookmark base p)=decide (p=6+3*n)
  bank : NativeMSBFold.laneBank counter base counterWidth c.work (BinarySeek.digitsAt a n) b
  flag : c.work (WorkLanes.address counter base 0)=
    decide (0 < BinaryCountdown.bankValue (BinarySeek.digitsAt a n) counterWidth)
  marker : c.work (WorkLanes.address counter base 3)=false
  other : ∀ other : Fin lanes, other ≠ counter → ∀ p,
    c.work (WorkLanes.address other base p)=
      columnsWork bookmark selected base initial.work n (WorkLanes.address other base p)
  sameIO : SameIO initial c
  frame : Frame (allocationFootprint lanes base counterWidth (BinaryCountdown.bankValue a counterWidth)) initial c

/-- A real binary counter controls the allocation loop. The resulting banks
and bookmark are located by tape bits; the finite table is independent of both
counter width and allocation count. Bookmark seeding and cleanup are separate. -/
theorem machine_exec {N : Main.Machine} {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : bookmark ∉ selected)
    (notCounter : counter ∉ selected) (distinct : counter ≠ bookmark)
    (input : List Bool) (c : Config N) (base counterWidth : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hhead : c.workHead = WorkLanes.address counter base 0)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (unique : ∀ p, c.work (WorkLanes.address bookmark base p) = decide (p=6))
    (marker : c.work (WorkLanes.address counter base 3)=false)
    (flag : c.work (WorkLanes.address counter base 0)=decide (0<BinaryCountdown.bankValue a counterWidth))
    (bank : NativeMSBFold.laneBank counter base counterWidth c.work a b) :
    ∃ d : Config (machine counter bookmark selected),
      FirstExit ((machine counter bookmark selected).step input)
        (fun _ e => e.workHead < allocationBound lanes base counterWidth (BinaryCountdown.bankValue a counterWidth) ∧
          Frame (allocationFootprint lanes base counterWidth (BinaryCountdown.bankValue a counterWidth)) c e)
        {e | e.state=none} (startOn (machine counter bookmark selected) c) d
        (WhileFlag.elapsed (iterationTime counter bookmark counterWidth) (BinaryCountdown.bankValue a counterWidth)+1) ∧
      d.workHead=WorkLanes.address counter base 0 ∧
      WorkLanes.OriginTrack lanes base d.work ∧
      (∀ p, d.work (WorkLanes.address bookmark base p)=decide (p=6+3*BinaryCountdown.bankValue a counterWidth)) ∧
      NativeMSBFold.laneBank counter base counterWidth d.work
        (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) b ∧
      BinaryCountdown.bankValue (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) counterWidth=0 ∧
      d.work (WorkLanes.address counter base 0)=false ∧
      d.work (WorkLanes.address counter base 3)=false ∧
      (∀ other : Fin lanes, other ≠ counter → ∀ p,
        d.work (WorkLanes.address other base p)=
          columnsWork bookmark selected base c.work (BinaryCountdown.bankValue a counterWidth)
            (WorkLanes.address other base p)) ∧ SameIO c d := by
  classical
  let A := body counter bookmark selected
  let count := BinaryCountdown.bankValue a counterWidth
  let bound := allocationBound lanes base counterWidth count
  let F := allocationFootprint lanes base counterWidth count
  let time := iterationTime counter bookmark counterWidth
  let P := Progress counter bookmark selected base counterWidth a b c
  let IA := fun (_ : ℕ) (_ : ℕ) (d : Config A) => d.workHead < bound ∧ Frame F c d
  let R := fun (n : ℕ) (s t : Config A) =>
    FirstExit (A.step input) (fun _ e => e.workHead < bound ∧ Frame F s e)
      {e | e.state=none} (WhileFlag.startBody A s) t (time n)
  let c0 : Config A := {c with state:=none}
  have p0 : P 0 c0 :=
    { head:=hhead,origin:=origin,book:=unique,bank:=bank,flag:=flag,marker:=marker
      other:=fun _ _ _ => rfl,sameIO:=⟨rfl,rfl,rfl,rfl⟩
      frame:=⟨fun _ _ => rfl,rfl,fun _ _ => rfl⟩ }
  have next : ∀ n < count, ∀ s, P n s → ∃ t, P (n+1) t ∧ R n s t := by
    intro n hn s hs
    have his : s.inputHead ≤ input.length+1 := by rw [hs.sameIO.1];exact hi
    have hcs : s.catalystHead ≤ s.catalyst.length := by rw [hs.sameIO.2.1,hs.sameIO.2.2.1];exact hc
    obtain ⟨t,HT,hth,hto,htbook,htflag,htbank,htmarker,htother,htIO⟩ :=
      body_exec counter bookmark selected notSelected notCounter distinct input s base (6+3*n)
        counterWidth (BinarySeek.digitsAt a n) b his hcs hs.head hs.origin hs.book hs.marker hs.bank
    have hN : count ≤ max count counterWidth := le_max_left _ _
    have hW : counterWidth ≤ max count counterWidth := le_max_right _ _
    have sizes : max (6+3*n+4) (7+3*counterWidth) ≤ 7+3*max count counterWidth := by
      apply max_le <;> omega
    have HB := firstExit_mono input s _ _ _ _ bound _ F HT
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ sizes) _)
      (by
        intro p hp
        rcases hp with hp|hp
        · exact ⟨by have H:=hp.1;omega,
            lt_of_lt_of_le hp.2 (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)⟩
        · rcases hp with ⟨q,hq,rfl⟩
          exact ⟨by dsimp [WorkLanes.address];omega,
            WorkLanes.address_lt_prefix counter base q _ (by exact lt_of_lt_of_le hq.2 (by omega))⟩)
      (by intro p hp; exact hp.elim (fun h => h) (fun h => h))
    have endFrame := (HB.during _ le_rfl _ HB.result).2
    refine ⟨t,?_,HB⟩
    exact
      { head:=hth
        origin:=hto
        book:=by simpa only [show 6+3*n+3=6+3*(n+1) by omega] using htbook
        bank:=htbank
        flag:=htflag
        marker:=htmarker
        other:=by
          intro lane hne p
          exact (htother lane hne p).trans
            (advanceWork_congr_point bookmark selected base (6+3*n) _ s.work _ (hs.other lane hne p))
        sameIO:=sameIO_trans hs.sameIO htIO
        frame:=hs.frame.trans endFrame }
  obtain ⟨phase,hzero,hP,hR⟩ := NativeFiniteIteration.exists_phases P R c0 p0 count next
  have phaseBound (n : ℕ) (hn : n ≤ count) : (phase n).workHead < bound := by
    rw [(hP n hn).head]
    exact WorkLanes.address_lt_prefix counter base 0 _ (by omega)
  have inputs (n : ℕ) (hn : n ≤ count) : (phase n).inputHead ≤ input.length+1 := by
    rw [(hP n hn).sameIO.1];exact hi
  have catalysts (n : ℕ) (hn : n ≤ count) : (phase n).catalystHead ≤ (phase n).catalyst.length := by
    rw [(hP n hn).sameIO.2.1,(hP n hn).sameIO.2.2.1];exact hc
  have flags : ∀ n < count, (phase n).work (phase n).workHead=true := by
    intro n hn
    rw [(hP n (by omega)).head,(hP n (by omega)).flag,
      BinarySeek.digitsAt_value a counterWidth n (by exact Nat.le_of_lt hn)]
    simp only [decide_eq_true_eq]
    change 0<count-n
    omega
  let I := fun (_ : ℕ) (d : Config (WhileFlag.machine A)) => d.workHead < bound ∧ Frame F c d
  have gate (n : ℕ) (hn : n ≤ count) (u : ℕ) : I u (WhileFlag.gateConfig A (phase n)) :=
    ⟨phaseBound n hn,(hP n hn).frame⟩
  have bodies : ∀ n < count, FirstExit (A.step input) (IA n) {e | e.state=none}
      (WhileFlag.startBody A (phase n)) (phase (n+1)) (time n) := by
    intro n hn
    have H := hR n hn
    exact { result:=H.result,exit_mem:=H.exit_mem,cut:=H.cut
            during:=fun u hu e he => ⟨(H.during u hu e he).1,
              (hP n (by omega)).frame.trans (H.during u hu e he).2⟩ }
  have phases : ∀ n < count, Segment ((WhileFlag.machine A).step input)
      (fun u d => I (WhileFlag.elapsed time n+u) d)
      (WhileFlag.gateConfig A (phase n)) (WhileFlag.gateConfig A (phase (n+1))) (1+time n) := by
    intro n hn
    apply WhileFlag.framed_phase A input (phase n) (phase (n+1)) (flags n hn)
      (inputs n (by omega)) (catalysts n (by omega)) (bodies n hn)
    · exact gate n (by omega) 0
    · intro u hu e he
      exact he
  have zero : BinaryCountdown.bankValue (BinarySeek.digitsAt a count) counterWidth=0 := by
    rw [BinarySeek.digitsAt_value a counterWidth count le_rfl]
    exact Nat.sub_self _
  have done : (phase count).work (phase count).workHead=false := by
    rw [(hP count le_rfl).head,(hP count le_rfl).flag,zero]
    rfl
  have exitInv : I (WhileFlag.elapsed time count+1) (WhileFlag.haltConfig A (phase count)) :=
    ⟨phaseBound count le_rfl,(hP count le_rfl).frame⟩
  have execution := WhileFlag.framed_loop A input phase time count I (gate 0 (by omega) 0) phases done
    (inputs count le_rfl) (catalysts count le_rfl) exitInv
  have H := WhileFlag.firstExit_loop A input phase time IA count I flags
    (fun n hn => inputs n (by omega)) (fun n hn => catalysts n (by omega)) bodies execution
  let d := WhileFlag.haltConfig A (phase count)
  refine ⟨d,?_,(hP count le_rfl).head,(hP count le_rfl).origin,(hP count le_rfl).book,
    (hP count le_rfl).bank,zero,?_,(hP count le_rfl).marker,(hP count le_rfl).other,(hP count le_rfl).sameIO⟩
  · simpa only [hzero,c0,WhileFlag.gateConfig,A,machine,WhileFlag.machine,startOn,I,bound,F,d,time,count] using H
  · change (phase count).work (WorkLanes.address counter base 0)=false
    rw [(hP count le_rfl).flag,zero]
    rfl

end CatalyticTreeEval.Contracts.NativeBankAllocate
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBankAllocateBounds -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeBankAllocate

theorem distance_le {lanes : ℕ} (counter bookmark : Fin lanes) :
    NativeLaneFlagCopy.distance counter bookmark ≤ lanes := by
  have hc:=counter.isLt
  have hb:=bookmark.isLt
  unfold NativeLaneFlagCopy.distance
  split_ifs <;> omega

theorem macroTime_le {lanes : ℕ} (counter : Fin lanes) :
    WorkLanes.macroTime counter ≤ 3*(lanes+1) := by
  dsimp [WorkLanes.macroTime,WorkLanes.distance]
  omega

theorem advanceTime_le {lanes : ℕ} (counter bookmark : Fin lanes) (row : ℕ) :
    advanceTime counter bookmark row ≤ (2*row+14)*(lanes+1) := by
  have hd:=distance_le counter bookmark
  have hb:=bookmark.isLt
  have hc:=counter.isLt
  have hbs:=Nat.sub_le lanes bookmark.val
  have hcs:=Nat.sub_le lanes counter.val
  dsimp [advanceTime]
  nlinarith

theorem iterationTime_le {lanes : ℕ} (counter bookmark : Fin lanes)
    (counterWidth n width : ℕ) (hc : counterWidth ≤ width) (hn : n ≤ width) :
    1+iterationTime counter bookmark counterWidth n ≤ 100*(lanes+1)*(width+1) := by
  have ha:=advanceTime_le counter bookmark (6+3*n)
  have hm:=macroTime_le counter
  have hm' := Nat.mul_le_mul_left (6*counterWidth+13) hm
  dsimp [iterationTime]
  nlinarith

/-- Native allocation is quadratic in the common bit bound, including every
marker traversal, every countdown and all while-controller transitions. -/
theorem allocationTime_le {lanes : ℕ} (counter bookmark : Fin lanes)
    (counterWidth count width : ℕ) (hc : counterWidth ≤ width) (hn : count ≤ width) :
    WhileFlag.elapsed (iterationTime counter bookmark counterWidth) count+1 ≤
      100*(lanes+1)*(width+1)^2+1 := by
  have H := Finset.sum_le_sum (s:=Finset.range count)
    (fun i hi => iterationTime_le counter bookmark counterWidth i width hc
      (by have h:=Finset.mem_range.mp hi;omega))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at H
  have H' := Nat.mul_le_mul_right (100*(lanes+1)*(width+1)) (show count ≤ width+1 by omega)
  dsimp [WhileFlag.elapsed]
  nlinarith

end CatalyticTreeEval.Contracts.NativeBankAllocate
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBankAllocateColumns -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeBankAllocate

theorem columns_inactive {lanes : ℕ} (bookmark lane : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : lane ∉ selected) (distinct : lane ≠ bookmark)
    (base : ℕ) (work : ℕ → Bool) (count p : ℕ) :
    columnsWork bookmark selected base work count (WorkLanes.address lane base p)=
      work (WorkLanes.address lane base p) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    change advanceWork bookmark selected base (6+3*n) (columnsWork bookmark selected base work n) _=_
    rw [advance_inactive bookmark lane selected notSelected distinct]
    exact ih

/-- A sweep cannot change a different column in a non-bookmark lane. -/
theorem advance_other_outside {lanes : ℕ} (bookmark lane : Fin lanes)
    (selected : Finset (Fin lanes)) (distinct : lane ≠ bookmark)
    (base row q : ℕ) (work : ℕ → Bool) (outside : q < row ∨ row+3 ≤ q) :
    advanceWork bookmark selected base row work (WorkLanes.address lane base q)=
      work (WorkLanes.address lane base q) := by
  have neq (r : ℕ) : WorkLanes.address lane base q ≠ WorkLanes.address bookmark base r := by
    intro he
    exact distinct (WorkLanes.address_lanes_injective lane bookmark base _ _ he).1
  have off : ¬(base+(lanes+1)*row ≤ WorkLanes.address lane base q ∧
      WorkLanes.address lane base q < base+(lanes+1)*row+BankColumnInitialize.steps lanes) := by
    rcases outside with before|after
    · have H := WorkLanes.address_lt_prefix lane base q row before
      omega
    · have H := Nat.mul_le_mul_left (lanes+1) after
      have E : base+(lanes+1)*row+BankColumnInitialize.steps lanes=base+(lanes+1)*(row+3) := by
        dsimp [BankColumnInitialize.steps]
        ring
      rw [E]
      dsimp [WorkLanes.address]
      omega
  rw [advanceWork,Function.update_of_ne (neq _),BankColumnInitialize.prefixWork,if_neg off,
    Function.update_of_ne (neq _)]

/-- Every completed selected column has the physical tag/A/B pattern. -/
theorem columns_initialized {lanes : ℕ} (bookmark lane : Fin lanes)
    (selected : Finset (Fin lanes)) (member : lane ∈ selected) (distinct : lane ≠ bookmark)
    (base : ℕ) (work : ℕ → Bool) (count : ℕ) :
    ∀ i < count, ∀ off : Fin 3,
      columnsWork bookmark selected base work count (WorkLanes.address lane base (6+3*i+off.val))=
        decide (off.val=0) := by
  induction count with
  | zero => intro i hi;omega
  | succ n ih =>
    intro i hi off
    change advanceWork bookmark selected base (6+3*n) (columnsWork bookmark selected base work n) _=_
    by_cases last : i=n
    · subst i
      exact advance_selected bookmark lane selected member distinct base (6+3*n) _ off
    · rw [advance_other_outside bookmark lane selected distinct base (6+3*n) (6+3*i+off.val) _
        (Or.inl (by have ho:=off.isLt;omega))]
      exact ih i (by omega) off

/-- No selected data past the last allocated column are overwritten. In
particular, the original blank false terminal remains an actual tape bit. -/
theorem columns_after {lanes : ℕ} (bookmark lane : Fin lanes)
    (selected : Finset (Fin lanes)) (distinct : lane ≠ bookmark)
    (base : ℕ) (work : ℕ → Bool) (count : ℕ) :
    ∀ q, 6+3*count ≤ q →
      columnsWork bookmark selected base work count (WorkLanes.address lane base q)=
        work (WorkLanes.address lane base q) := by
  induction count with
  | zero => intro q _;rfl
  | succ n ih =>
    intro q hq
    change advanceWork bookmark selected base (6+3*n) (columnsWork bookmark selected base work n) _=_
    rw [advance_other_outside bookmark lane selected distinct base (6+3*n) q _ (Or.inr (by omega))]
    exact ih q (by omega)

theorem columns_prefix {lanes : ℕ} (bookmark lane : Fin lanes)
    (selected : Finset (Fin lanes)) (distinct : lane ≠ bookmark)
    (base : ℕ) (work : ℕ → Bool) (count q : ℕ) (hq : q < 6) :
    columnsWork bookmark selected base work count (WorkLanes.address lane base q)=
      work (WorkLanes.address lane base q) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    change advanceWork bookmark selected base (6+3*n) (columnsWork bookmark selected base work n) _=_
    rw [advance_other_outside bookmark lane selected distinct base (6+3*n) q _ (Or.inl (by omega))]
    exact ih

/-- The loop endpoint is a genuine zero-valued tagged bank, with its original
false terminator. No initialization assumption is hidden in a bank interface. -/
theorem columns_bank {lanes : ℕ} (bookmark lane : Fin lanes)
    (selected : Finset (Fin lanes)) (member : lane ∈ selected) (distinct : lane ≠ bookmark)
    (base : ℕ) (work : ℕ → Bool) (count : ℕ)
    (terminal : work (WorkLanes.address lane base (6+3*count))=false) :
    NativeMSBFold.laneBank lane base count (columnsWork bookmark selected base work count)
      (fun _ => false) (fun _ => false) := by
  constructor
  · change columnsWork bookmark selected base work count (WorkLanes.address lane base (6+3*count))=false
    rw [columns_after bookmark lane selected distinct base work count _ le_rfl]
    exact terminal
  · intro i hi
    exact ⟨columns_initialized bookmark lane selected member distinct base work count i hi (0:Fin 3),
      columns_initialized bookmark lane selected member distinct base work count i hi (1:Fin 3),
      columns_initialized bookmark lane selected member distinct base work count i hi (2:Fin 3)⟩

end CatalyticTreeEval.Contracts.NativeBankAllocate
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBankAllocateFull -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace CatalyticTreeEval.Contracts.NativeBankAllocateFull

open NativeRoundSupport
open RestoringRound (SameIO)
open NativeLaneWordTransfer (sameIO_trans)

/-- Complete charged allocation from blank selected/bookmark lanes and a real
counter bank. The counter's preserved B field is reusable after A is consumed.
The temporary bookmark is completely erased, with no saved runtime address. -/
theorem machine_exec {N : Main.Machine} {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : bookmark ∉ selected)
    (notCounter : counter ∉ selected) (distinct : counter ≠ bookmark)
    (input : List Bool) (c : Config N) (base counterWidth : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=WorkLanes.address counter base 0)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (blankBook : ∀ p, c.work (WorkLanes.address bookmark base p)=false)
    (blankSelected : ∀ lane ∈ selected, ∀ p, c.work (WorkLanes.address lane base p)=false)
    (marker : c.work (WorkLanes.address counter base 3)=false)
    (flag : c.work (WorkLanes.address counter base 0)=decide (0<BinaryCountdown.bankValue a counterWidth))
    (bank : NativeMSBFold.laneBank counter base counterWidth c.work a b) :
    ∃ d : Config (machine counter bookmark selected),
      FirstExit ((machine counter bookmark selected).step input)
        (fun _ e => e.workHead < NativeBankAllocate.allocationBound lanes base counterWidth (BinaryCountdown.bankValue a counterWidth) ∧
          Frame (NativeBankAllocate.allocationFootprint lanes base counterWidth (BinaryCountdown.bankValue a counterWidth)) c e)
        {e | e.state=none} (startOn (machine counter bookmark selected) c) d
        (seedTime counter bookmark+
          ((WhileFlag.elapsed (NativeBankAllocate.iterationTime counter bookmark counterWidth)
            (BinaryCountdown.bankValue a counterWidth)+1)+cleanupTime counter bookmark (BinaryCountdown.bankValue a counterWidth))) ∧
      d.workHead=WorkLanes.address counter base 0 ∧ WorkLanes.OriginTrack lanes base d.work ∧
      (∀ p, d.work (WorkLanes.address bookmark base p)=false) ∧
      NativeMSBFold.laneBank counter base counterWidth d.work
        (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) b ∧
      BinaryCountdown.bankValue (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) counterWidth=0 ∧
      d.work (WorkLanes.address counter base 0)=false ∧
      d.work (WorkLanes.address counter base 3)=false ∧
      (∀ lane ∈ selected, NativeMSBFold.laneBank lane base (BinaryCountdown.bankValue a counterWidth)
        d.work (fun _ => false) (fun _ => false)) ∧
      (∀ lane ∈ selected, ∀ p < 6, d.work (WorkLanes.address lane base p)=false) ∧
      (∀ lane : Fin lanes, lane ≠ counter → lane ≠ bookmark → lane ∉ selected → ∀ p,
        d.work (WorkLanes.address lane base p)=c.work (WorkLanes.address lane base p)) ∧ SameIO c d := by
  let count:=BinaryCountdown.bankValue a counterWidth
  let A:=NativeBookmarkHome.seed counter bookmark
  let B:=NativeBankAllocate.machine counter bookmark selected
  let C:=NativeBookmarkHome.cleanup counter bookmark
  let bound:=NativeBankAllocate.allocationBound lanes base counterWidth count
  let F:=NativeBankAllocate.allocationFootprint lanes base counterWidth count
  have memCell (lane : Fin lanes) (p : ℕ) (hp : p < 7+3*max count counterWidth) :
      WorkLanes.address lane base p ∈ F.work :=
    ⟨by dsimp [WorkLanes.address];omega,WorkLanes.address_lt_prefix lane base p _ hp⟩
  have different (lane : Fin lanes) (hne : lane ≠ bookmark) (p q : ℕ) :
      WorkLanes.address lane base p ≠ WorkLanes.address bookmark base q := by
    intro he
    exact hne (WorkLanes.address_lanes_injective lane bookmark base _ _ he).1
  obtain ⟨ds,HS,hsh,hsw,hso,hsbook,hsIO⟩ := NativeBookmarkHome.seed_exec counter bookmark input c base hi hc head origin blankBook
  have retainedS (p : ℕ) : ds.work (WorkLanes.address counter base p)=c.work (WorkLanes.address counter base p) := by
    rw [hsw,Function.update_of_ne (different counter distinct p 6)]
  have his : ds.inputHead ≤ input.length+1 := by rw [hsIO.1];exact hi
  have hcs : ds.catalystHead ≤ ds.catalyst.length := by rw [hsIO.2.1,hsIO.2.2.1];exact hc
  have bankS : NativeMSBFold.laneBank counter base counterWidth ds.work a b := by
    change ShiftAppend.bankContents (fun p => ds.work (WorkLanes.address counter base p)) 6 counterWidth a b
    rw [show (fun p => ds.work (WorkLanes.address counter base p))=
      (fun p => c.work (WorkLanes.address counter base p)) from funext retainedS]
    exact bank
  obtain ⟨dl,HL,hlh,hlo,hlbook,hlbank,hlzero,hlflag,hlmarker,hlother,hlIO⟩ :=
    NativeBankAllocate.machine_exec counter bookmark selected notSelected notCounter distinct input ds base counterWidth a b
      his hcs hsh hso hsbook ((retainedS 3).trans marker) ((retainedS 0).trans flag) bankS
  have ioL:=sameIO_trans hsIO hlIO
  have hil : dl.inputHead ≤ input.length+1 := by rw [ioL.1];exact hi
  have hcl : dl.catalystHead ≤ dl.catalyst.length := by rw [ioL.2.1,ioL.2.2.1];exact hc
  obtain ⟨dc,HC,hch,hcw,hco,hcbook,hcIO⟩ := NativeBookmarkHome.cleanup_exec counter bookmark input dl base (6+3*count)
    hil hcl hlh hlo hlbook
  have retainedC (lane : Fin lanes) (hne : lane ≠ bookmark) (p : ℕ) :
      dc.work (WorkLanes.address lane base p)=dl.work (WorkLanes.address lane base p) := by
    rw [hcw,Function.update_of_ne (different lane hne p (6+3*count))]
  have HSF:=firstExit_mono input c _ _ _ _ bound _ F HS
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)
    (by intro p hp;rcases Set.mem_singleton_iff.mp hp with rfl;exact memCell bookmark 6 (by omega)) (by simp)
  have HCF:=firstExit_mono input dl _ _ _ _ bound _ F HC
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by have H:=le_max_left count counterWidth;omega)) _)
    (by
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      exact memCell bookmark (6+3*count) (by have H:=le_max_left count counterWidth;omega)) (by simp)
  let tl:=WhileFlag.elapsed (NativeBankAllocate.iterationTime counter bookmark counterWidth) count+1
  have HLC:=framed_seq B C input ds dl dc tl (cleanupTime counter bookmark count) bound F HL HCF
  let e:=Sequential.rightConfig B C dc
  have H:=framed_seq A (Sequential.machine B C) input c ds e (seedTime counter bookmark)
    (tl+cleanupTime counter bookmark count) bound F HSF HLC
  let d:=Sequential.rightConfig A (Sequential.machine B C) e
  have notBook (lane : Fin lanes) (member : lane ∈ selected) : lane ≠ bookmark := by
    intro he
    subst lane
    exact notSelected member
  have notCount (lane : Fin lanes) (member : lane ∈ selected) : lane ≠ counter := by
    intro he
    subst lane
    exact notCounter member
  have selectedWork (lane : Fin lanes) (member : lane ∈ selected) (p : ℕ) :
      dc.work (WorkLanes.address lane base p)=
        NativeBankAllocate.columnsWork bookmark selected base ds.work count (WorkLanes.address lane base p) := by
    rw [retainedC lane (notBook lane member) p,hlother lane (notCount lane member) p]
  refine ⟨d,H,hch,hco,hcbook,?_,hlzero,?_,?_,?_,?_,?_,sameIO_trans ioL hcIO⟩
  · change NativeMSBFold.laneBank counter base counterWidth dc.work _ b
    change ShiftAppend.bankContents (fun p => dc.work (WorkLanes.address counter base p)) 6 counterWidth _ b
    rw [show (fun p => dc.work (WorkLanes.address counter base p))=
      (fun p => dl.work (WorkLanes.address counter base p)) from funext (retainedC counter distinct)]
    exact hlbank
  · change dc.work _=false
    rw [retainedC counter distinct 0,hlflag]
  · change dc.work _=false
    rw [retainedC counter distinct 3,hlmarker]
  · intro lane member
    change ShiftAppend.bankContents (fun p => dc.work (WorkLanes.address lane base p)) 6 count _ _
    rw [show (fun p => dc.work (WorkLanes.address lane base p))=
      (fun p => NativeBankAllocate.columnsWork bookmark selected base ds.work count (WorkLanes.address lane base p)) from
      funext (selectedWork lane member)]
    apply NativeBankAllocate.columns_bank bookmark lane selected member (notBook lane member) base ds.work count
    rw [hsw,Function.update_of_ne (different lane (notBook lane member) _ 6)]
    exact blankSelected lane member _
  · intro lane member p hp
    change dc.work _=false
    rw [selectedWork lane member p,NativeBankAllocate.columns_prefix bookmark lane selected (notBook lane member) base ds.work count p hp,
      hsw,Function.update_of_ne (different lane (notBook lane member) p 6)]
    exact blankSelected lane member p
  · intro lane hnc hnb hns p
    change dc.work _=c.work _
    rw [retainedC lane hnb p,hlother lane hnc p,
      NativeBankAllocate.columns_inactive bookmark lane selected hns hnb base ds.work count p,
      hsw,Function.update_of_ne (different lane hnb p 6)]

end CatalyticTreeEval.Contracts.NativeBankAllocateFull
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeCatalystStationary -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeArithmeticStationary -/
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

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBankAllocateResource -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeBankAllocateFull

open NativeHeadStationary

theorem seedTime_le {lanes : ℕ} (counter bookmark : Fin lanes) :
    seedTime counter bookmark ≤ 30*(lanes+1) := by
  have hd:=NativeBankAllocate.distance_le counter bookmark
  have hb:=bookmark.isLt
  have hc:=counter.isLt
  have hbs:=Nat.sub_le lanes bookmark.val
  have hcs:=Nat.sub_le lanes counter.val
  dsimp [seedTime,NativeBookmarkHome.time]
  nlinarith

theorem cleanupTime_le {lanes : ℕ} (counter bookmark : Fin lanes) (count width : ℕ) (hn : count ≤ width) :
    cleanupTime counter bookmark count ≤ 30*(lanes+1)*(width+1) := by
  have hd:=NativeBankAllocate.distance_le counter bookmark
  have hb:=bookmark.isLt
  have hc:=counter.isLt
  have hbs:=Nat.sub_le lanes bookmark.val
  have hcs:=Nat.sub_le lanes counter.val
  dsimp [cleanupTime,NativeBookmarkHome.time]
  nlinarith

/-- Includes the initial marker, every allocated column, the consumed binary
counter and final bookmark erasure. No setup or return traversal is free. -/
theorem time_le {lanes : ℕ} (counter bookmark : Fin lanes)
    (counterWidth count width : ℕ) (hc : counterWidth ≤ width) (hn : count ≤ width) :
    seedTime counter bookmark+
      ((WhileFlag.elapsed (NativeBankAllocate.iterationTime counter bookmark counterWidth) count+1)+
        cleanupTime counter bookmark count) ≤ 200*(lanes+1)*(width+1)^2+1 := by
  have hs:=seedTime_le counter bookmark
  have hl:=NativeBankAllocate.allocationTime_le counter bookmark counterWidth count width hc hn
  have he:=cleanupTime_le counter bookmark count width hn
  nlinarith

private theorem markerStationary (head : Head) (direction : CatalyticMatching.General.Move) (lanes : ℕ) :
    Stationary head (NativeMarkerSeek.machine direction lanes) := by
  intro q input work catalyst io wo co
  by_cases h : q.val=0 ∧ work=true <;> cases head <;> simp [motion,NativeMarkerSeek.machine,h]

private theorem columnStationary (head : Head) (lanes : ℕ) (selected : Finset (Fin lanes)) :
    Stationary head (BankColumnInitialize.machine lanes selected) := by
  intro q input work catalyst io wo co
  cases head <;> rfl

private theorem advanceStationary {lanes : ℕ} (head : Head) (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) : Stationary head (NativeBankAllocate.advance counter bookmark selected) :=
  sequential head _ _ (moveFlag head counter bookmark)
    (sequential head _ _ (markerStationary head .right lanes)
      (sequential head _ _ (literal head .stay 0 (some false))
        (sequential head _ _ (literal head .left bookmark.val none)
          (sequential head _ _ (columnStationary head lanes selected)
            (sequential head _ _ (literal head .right bookmark.val (some true))
              (sequential head _ _ (literal head .right (lanes-bookmark.val) none)
                (sequential head _ _ (markerStationary head .left lanes)
                  (literal head .left (lanes-counter.val) none))))))))

private theorem homeStationary {lanes : ℕ} (head : Head) (counter bookmark : Fin lanes) :
    Stationary head (NativeBookmarkHome.machine counter bookmark) :=
  sequential head _ _ (literal head .right (lanes-bookmark.val) none)
    (sequential head _ _ (markerStationary head .left lanes) (literal head .left (lanes-counter.val) none))

theorem stationary {lanes : ℕ} (head : Head) (counter bookmark : Fin lanes) (selected : Finset (Fin lanes)) :
    Stationary head (machine counter bookmark selected) := by
  have seedH : Stationary head (NativeBookmarkHome.seed counter bookmark) :=
    sequential head _ _ (moveFlag head counter bookmark)
      (sequential head _ _ (literal head .right (6*(lanes+1)) (some true)) (homeStationary head counter bookmark))
  have bodyH : Stationary head (NativeBankAllocate.body counter bookmark selected) :=
    sequential head _ _ (advanceStationary head counter bookmark selected)
      (workLanes head _ _ _ (countdown head))
  have loopH : Stationary head (NativeBankAllocate.machine counter bookmark selected) := whileFlag head _ bodyH
  have clearH : Stationary head (NativeBookmarkHome.clear counter bookmark) :=
    sequential head _ _ (literal head .stay 0 (some false)) (homeStationary head counter bookmark)
  have cleanupH : Stationary head (NativeBookmarkHome.cleanup counter bookmark) :=
    sequential head _ _ (moveFlag head counter bookmark)
      (sequential head _ _ (markerStationary head .right lanes) clearH)
  exact sequential head _ _ seedH (sequential head _ _ loopH cleanupH)

end CatalyticTreeEval.Contracts.NativeBankAllocateFull
end

/- Proof component: Solutions.CatalyticTreeEvaluation.NativeBankAllocationAPI -/
section

set_option autoImplicit false
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace CatalyticTreeEval.Contracts.NativeBankAllocateFull

/-- The public allocation contract uses only the native model and public
memory contracts. Every initialized bank and the cleared bookmark are physical. -/
theorem allocation_exec {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : bookmark ∉ selected)
    (notCounter : counter ∉ selected) (distinct : counter ≠ bookmark)
    (input : List Bool) (c : Config (machine counter bookmark selected))
    (base counterWidth width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=WorkLanes.address counter base 0)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (blankBook : ∀ p, c.work (WorkLanes.address bookmark base p)=false)
    (blankSelected : ∀ lane ∈ selected, ∀ p, c.work (WorkLanes.address lane base p)=false)
    (marker : c.work (WorkLanes.address counter base 3)=false)
    (flag : c.work (WorkLanes.address counter base 0)=decide (0<BinaryCountdown.bankValue a counterWidth))
    (bank : ShiftAppend.bankContents (fun p => c.work (WorkLanes.address counter base p)) 6 counterWidth a b)
    (counterFits : counterWidth ≤ width) (countFits : BinaryCountdown.bankValue a counterWidth ≤ width) :
    ∃ (d : Config (machine counter bookmark selected)) (T : ℕ),
      FirstExit ((machine counter bookmark selected).step input)
        (fun _ e => (Envelope.mk 0 (base+(lanes+1)*(7+3*max (BinaryCountdown.bankValue a counterWidth) counterWidth))
          c.catalystHead (c.catalystHead+1)).Contains e ∧
          SameOutside ⟨Set.Ico base (base+(lanes+1)*(7+3*max (BinaryCountdown.bankValue a counterWidth) counterWidth)),∅⟩ c e)
        {e | e.state=none} {c with state:=some (machine counter bookmark selected).start} d T ∧
      T ≤ 200*(lanes+1)*(width+1)^2+1 ∧
      d.workHead=WorkLanes.address counter base 0 ∧ WorkLanes.OriginTrack lanes base d.work ∧
      (∀ p, d.work (WorkLanes.address bookmark base p)=false) ∧
      ShiftAppend.bankContents (fun p => d.work (WorkLanes.address counter base p)) 6 counterWidth
        (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) b ∧
      BinaryCountdown.bankValue (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) counterWidth=0 ∧
      d.work (WorkLanes.address counter base 0)=false ∧
      d.work (WorkLanes.address counter base 3)=false ∧
      (∀ lane ∈ selected, ShiftAppend.bankContents (fun p => d.work (WorkLanes.address lane base p))
        6 (BinaryCountdown.bankValue a counterWidth) (fun _ => false) (fun _ => false)) ∧
      (∀ lane ∈ selected, ∀ p < 6, d.work (WorkLanes.address lane base p)=false) ∧
      SavedPrefix base c d ∧ d.catalyst=c.catalyst ∧ d.output=c.output := by
  let M:=machine counter bookmark selected
  let count:=BinaryCountdown.bankValue a counterWidth
  let bound:=base+(lanes+1)*(7+3*max count counterWidth)
  let F : Footprint:=⟨Set.Ico base bound,∅⟩
  obtain ⟨d,H,hdh,hdo,hdb,hdbank,hdzero,hdf,hdm,hds,hdprefix,_,hdIO⟩ :=
    machine_exec counter bookmark selected notSelected notCounter distinct input c base counterWidth a b
      hi hc head origin blankBook blankSelected marker flag bank
  let T:=seedTime counter bookmark+
    ((WhileFlag.elapsed (NativeBankAllocate.iterationTime counter bookmark counterWidth) count+1)+
      cleanupTime counter bookmark count)
  have HE := NativeHeadStationary.firstExit_envelope input (NativeRoundSupport.startOn M c) d T bound F
    (stationary .catalyst counter bookmark selected) H
  refine ⟨d,T,HE,time_le counter bookmark counterWidth count width counterFits countFits,
    hdh,hdo,hdb,hdbank,hdzero,hdf,hdm,hds,hdprefix,?_,hdIO.2.2.1,hdIO.2.2.2⟩
  intro p hp
  exact (H.during T le_rfl d H.result).2.1 p (by intro h;exact Nat.not_le_of_lt hp h.1)

end CatalyticTreeEval.Contracts.NativeBankAllocateFull
end


open CatalyticTreeEval.Contracts CatalyticTreeEval.Contracts.NativeBankAllocateFull

theorem solution {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : bookmark ∉ selected)
    (notCounter : counter ∉ selected) (distinct : counter ≠ bookmark)
    (input : List Bool) (c : Config (machine counter bookmark selected))
    (base counterWidth width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=WorkLanes.address counter base 0)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (blankBook : ∀ p, c.work (WorkLanes.address bookmark base p)=false)
    (blankSelected : ∀ lane ∈ selected, ∀ p, c.work (WorkLanes.address lane base p)=false)
    (marker : c.work (WorkLanes.address counter base 3)=false)
    (flag : c.work (WorkLanes.address counter base 0)=decide (0<BinaryCountdown.bankValue a counterWidth))
    (bank : ShiftAppend.bankContents (fun p => c.work (WorkLanes.address counter base p)) 6 counterWidth a b)
    (counterFits : counterWidth ≤ width) (countFits : BinaryCountdown.bankValue a counterWidth ≤ width) :
    ∃ (d : Config (machine counter bookmark selected)) (T : ℕ),
      FirstExit ((machine counter bookmark selected).step input)
        (fun _ e => (Envelope.mk 0 (base+(lanes+1)*(7+3*max (BinaryCountdown.bankValue a counterWidth) counterWidth))
          c.catalystHead (c.catalystHead+1)).Contains e ∧
          SameOutside ⟨Set.Ico base (base+(lanes+1)*(7+3*max (BinaryCountdown.bankValue a counterWidth) counterWidth)),∅⟩ c e)
        {e | e.state=none} {c with state:=some (machine counter bookmark selected).start} d T ∧
      T ≤ 200*(lanes+1)*(width+1)^2+1 ∧
      d.workHead=WorkLanes.address counter base 0 ∧ WorkLanes.OriginTrack lanes base d.work ∧
      (∀ p, d.work (WorkLanes.address bookmark base p)=false) ∧
      ShiftAppend.bankContents (fun p => d.work (WorkLanes.address counter base p)) 6 counterWidth
        (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) b ∧
      BinaryCountdown.bankValue (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) counterWidth=0 ∧
      d.work (WorkLanes.address counter base 0)=false ∧
      d.work (WorkLanes.address counter base 3)=false ∧
      (∀ lane ∈ selected, ShiftAppend.bankContents (fun p => d.work (WorkLanes.address lane base p))
        6 (BinaryCountdown.bankValue a counterWidth) (fun _ => false) (fun _ => false)) ∧
      (∀ lane ∈ selected, ∀ p < 6, d.work (WorkLanes.address lane base p)=false) ∧
      SavedPrefix base c d ∧ d.catalyst=c.catalyst ∧ d.output=c.output := by
  exact CatalyticTreeEval.Contracts.NativeBankAllocateFull.allocation_exec counter bookmark selected notSelected notCounter distinct input c base counterWidth width a b hi hc head origin blankBook blankSelected marker flag bank counterFits countFits
