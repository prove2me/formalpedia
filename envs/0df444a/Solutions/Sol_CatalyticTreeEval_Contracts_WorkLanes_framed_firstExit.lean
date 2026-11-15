-- Prove2me | solution 1 for CatalyticTreeEval.Contracts.WorkLanes.framed_firstExit
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T06:45:17.609169+00:00
-- url     : https://prove2.me/submissions/98af9399-9b54-4e12-a0f7-c61c7f961eba

import Definitions.Def_CatalyticTreeEval_WorkLaneContracts



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


theorem solution (A : CatalyticTreeEval.Main.Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
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
  exact CatalyticTreeEval.Contracts.WorkLanes.framed_firstExit A lanes lane base input source target physical T E F hi hc origin workMatches H
