-- Prove2me | solution 1 for CatalyticTreeEval.Contracts.FinitePrinter.printsIn_of_prints
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T06:27:28.127893+00:00
-- url     : https://prove2.me/submissions/0c3d815a-b6bd-4209-9c7f-59a9697fbdc3

import Definitions.Def_CatalyticTreeEval_FinitePrinter



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


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.FinitePrinter

open CatalyticMatching.General

theorem quiet_commutes (M : Machine) (input : List Bool) (c : Configuration M) :
    quietStep M input (eraseOutput c) = (M.step input c).map eraseOutput := by
  cases c with
  | mk state ih wh ch work catalyst output =>
    cases state with
    | none => rfl
    | some q =>
        simp only [quietStep, eraseOutput, Machine.step]
        try dsimp only
        split_ifs <;> simp_all [eraseOutput]

theorem quiet_run (M : Machine) (input : List Bool) (c : Configuration M) (t : ℕ) :
    runFrom (quietStep M input) (eraseOutput c) t =
      (runFrom (M.step input) c t).map eraseOutput :=
  runFrom_map (M.step input) (quietStep M input) eraseOutput (quiet_commutes M input) c t

theorem core_injective (M : Machine) (inputLength bound : ℕ)
    {c d : Configuration M}
    (hci : c.inputHead ≤ inputLength + 1) (hdi : d.inputHead ≤ inputLength + 1)
    (hcw : c.workHead < bound) (hdw : d.workHead < bound)
    (hcc : c.catalyst = []) (hdc : d.catalyst = [])
    (hch : c.catalystHead = 0) (hdh : d.catalystHead = 0)
    (hct : ∀ p, bound ≤ p → c.work p = false)
    (hdt : ∀ p, bound ≤ p → d.work p = false)
    (same : core M inputLength bound c hci hcw = core M inputLength bound d hdi hdw) :
    eraseOutput c = eraseOutput d := by
  have state : c.state = d.state := congrArg Prod.fst same
  have inputHead : c.inputHead = d.inputHead :=
    congrArg (fun v : PrinterCore M inputLength bound => v.2.1.val) same
  have workHead : c.workHead = d.workHead :=
    congrArg (fun v : PrinterCore M inputLength bound => v.2.2.1.val) same
  have bits : (fun p : Fin bound => c.work p.val) = (fun p : Fin bound => d.work p.val) :=
    congrArg (fun v : PrinterCore M inputLength bound => v.2.2.2) same
  have work : c.work = d.work := by
    funext p
    by_cases hp : p < bound
    · exact congrFun bits ⟨p, hp⟩
    · rw [hct p (by omega), hdt p (by omega)]
  cases c
  cases d
  simp_all [eraseOutput]

theorem first_halt (M : Machine) (input tape : List Bool)
    {t : ℕ} {d : Configuration M} (result : M.run input tape t = some d)
    (halt : d.state = none) :
    ∃ s ≤ t, FirstExit (M.step input) (fun _ _ => True) {c | c.state = none}
      (M.initial tape) d s := by
  have existsHalt : ∃ s, ∃ c : Configuration M,
      M.run input tape s = some c ∧ c.state = none := ⟨t, d, result, halt⟩
  let s := Nat.find existsHalt
  obtain ⟨c, hc, stopped⟩ := Nat.find_spec existsHalt
  have bound : s ≤ t := Nat.find_min' existsHalt ⟨d, result, halt⟩
  have final : c = d := by
    have H := result
    rw [← runFrom_initial] at H
    rw [show t = s + (t - s) by omega, runFrom_add,
      show runFrom (M.step input) (M.initial tape) s = some c by
        simpa only [runFrom_initial] using hc] at H
    rw [Option.bind_some, runFrom_halted M input c stopped] at H
    exact Option.some.inj H
  subst d
  refine ⟨s, bound, ?_⟩
  refine ⟨⟨by simpa only [runFrom_initial] using hc, by intros; trivial⟩, stopped, ?_⟩
  intro u hu e he hstate
  exact Nat.find_min existsHalt hu ⟨e, by simpa only [runFrom_initial] using he, hstate⟩

theorem card_core (M : Machine) (inputLength bound : ℕ) :
    Fintype.card (PrinterCore M inputLength bound) = configurationBound M inputLength bound := by
  simp [PrinterCore, configurationBound, Nat.mul_assoc]

/-- A first-halting bounded printer has no repeated finite configuration key.
The key omits unreadable output and the untouched blank work suffix. -/
theorem firstExit_time_lt (M : Machine) (input : List Bool) {d : Configuration M} {T bound : ℕ}
    (H : FirstExit (M.step input) (fun _ _ => True) {c | c.state = none} (M.initial []) d T)
    (work : M.workBound input [] T bound) : T < configurationBound M input.length bound := by
  classical
  let visited (i : Fin (T + 1)) := H.toSegment.at (Nat.le_of_lt_succ i.isLt)
  let cfg (i : Fin (T + 1)) : Configuration M := Classical.choose (visited i)
  have reached (i : Fin (T + 1)) : M.run input [] i.val = some (cfg i) := by
    have raw : runFrom (M.step input) (M.initial []) i.val = some (cfg i) :=
      (Classical.choose_spec (visited i)).1
    rw [runFrom_initial] at raw
    exact raw
  have hinput (i : Fin (T + 1)) := (run_headBounds M input [] (reached i)).1
  have hwork (i : Fin (T + 1)) := work i.val (Nat.le_of_lt_succ i.isLt) (cfg i) (reached i)
  have hcatalyst (i : Fin (T + 1)) : (cfg i).catalyst = [] :=
    List.eq_nil_of_length_eq_zero (run_catalyst_length M input [] (reached i))
  have hhead (i : Fin (T + 1)) : (cfg i).catalystHead = 0 := by
    have hi := (run_headBounds M input [] (reached i)).2
    simpa only [hcatalyst i, List.length_nil, Nat.le_zero] using hi
  have hblank (i : Fin (T + 1)) : ∀ p, bound ≤ p → (cfg i).work p = false :=
    run_work_zero_above M input [] work i.val (Nat.le_of_lt_succ i.isLt) (cfg i) (reached i)
  let encode (i : Fin (T + 1)) : PrinterCore M input.length bound :=
    core M input.length bound (cfg i) (hinput i) (hwork i)
  have quiet : FirstExit (quietStep M input) (fun _ _ => True) {c | c.state = none}
      (eraseOutput (M.initial [])) (eraseOutput d) T := by
    refine ⟨H.toSegment.map (I := fun _ _ => True) eraseOutput (quiet_commutes M input)
      (fun _ _ _ _ => True.intro), H.exit_mem, ?_⟩
    intro u hu c hc
    rw [quiet_run] at hc
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact H.cut u hu e he
  have injective : Function.Injective encode := by
    intro i j same
    have equal : eraseOutput (cfg i) = eraseOutput (cfg j) :=
      core_injective M input.length bound (hinput i) (hinput j) (hwork i) (hwork j)
        (hcatalyst i) (hcatalyst j) (hhead i) (hhead j) (hblank i) (hblank j) same
    have qi : runFrom (quietStep M input) (eraseOutput (M.initial [])) i.val =
        some (eraseOutput (cfg i)) := by
      rw [quiet_run, runFrom_initial, reached i]
      rfl
    have qj : runFrom (quietStep M input) (eraseOutput (M.initial [])) j.val =
        some (eraseOutput (cfg i)) := by
      rw [quiet_run, runFrom_initial, reached j, equal]
      rfl
    exact Fin.ext (quiet.time_injective (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) qi qj)
  have count := Fintype.card_le_of_injective encode injective
  rw [Fintype.card_fin, card_core] at count
  omega

/-- A space-only native printer admits a bounded-time certificate for the same
machine and output. The input-length factor and finite control are explicit. -/
theorem printsIn_of_prints (M : Main.Machine) (input output : List Bool) (space : ℝ)
    (prints : Main.Prints M input output space) :
    Main.PrintsIn M input output space
      (configurationBound M input.length ⌈space⌉₊ : ℝ) := by
  obtain ⟨t, d, hr, halt, out, work⟩ := prints
  obtain ⟨s, short, first⟩ := first_halt M input [] hr halt
  have work' : M.workBound input [] s ⌈space⌉₊ :=
    fun u hu e he => work u (hu.trans short) e he
  have time := firstExit_time_lt M input first work'
  refine ⟨s, d, ?_, halt, out, work', ?_⟩
  · simpa only [runFrom_initial] using first.result
  · exact_mod_cast time.le

end CatalyticTreeEval.Contracts.FinitePrinter


theorem solution (M : CatalyticTreeEval.Main.Machine) (input output : List Bool) (space : ℝ)
    (prints : CatalyticTreeEval.Main.Prints M input output space) :
    CatalyticTreeEval.Main.PrintsIn M input output space
      (CatalyticTreeEval.Contracts.FinitePrinter.configurationBound M input.length ⌈space⌉₊ : ℝ) := by
  exact CatalyticTreeEval.Contracts.FinitePrinter.printsIn_of_prints M input output space prints
