-- Prove2me | solution 1 for CatalyticTreeEval.Contracts.TaggedReturn.framed_firstExit
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T09:42:37.600852+00:00
-- url     : https://prove2.me/submissions/3811ff73-fc7b-4827-b2a6-1918ae720d9c

import Definitions.Def_CatalyticTreeEval_TaggedReturn



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
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false

namespace CatalyticTreeEval.Contracts.TaggedReturn

open CatalyticMatching.General

theorem states_eq (A : Machine) (tags : ℕ) :
    (machine A tags).states = (tags + 1) * (A.states + 1) := by
  simp [machine, Control]

theorem embed_entry (A : Machine) (tags : ℕ) (tag : Fin (tags + 1))
    (c : Configuration A) (state : c.state = some A.start) :
    (embed A tags tag c).state = some (entry A tags tag) := by
  simp only [embed, entry, state]

/-- Leaving the tagged port costs a further actual quiet transition. A caller
which redirects this port must charge that dispatch rather than dropping it. -/
theorem return_step (A : Machine) (tags : ℕ) (tag : Fin (tags + 1)) (input : List Bool)
    (c : Configuration A) (state : c.state = none)
    (hi : c.inputHead ≤ input.length + 1) (hc : c.catalystHead ≤ c.catalyst.length) :
    (machine A tags).step input (embed A tags tag c) =
      some { (embed A tags tag c) with state := none } := by
  simp [Machine.step, embed, machine, Equiv.symm_apply_apply, state,
    Move.apply, hi, hc, Function.update_eq_self]

theorem step_live (A : Machine) (tags : ℕ) (tag : Fin (tags + 1)) (input : List Bool)
    (c d : Configuration A) (q : Fin A.states) (state : c.state = some q)
    (step : A.step input c = some d) :
    (machine A tags).step input (embed A tags tag c) = some (embed A tags tag d) := by
  simp only [Machine.step, state] at step
  let a := A.table q (if c.inputHead = 0 then none else input[c.inputHead - 1]?)
    (c.work c.workHead) c.catalyst[c.catalystHead]?
    (c.inputHead == 0) (c.workHead == 0) (c.catalystHead == 0)
  change (if a.inputMove.apply c.inputHead ≤ input.length + 1 ∧
      a.catalystMove.apply c.catalystHead ≤ c.catalyst.length ∧
      (a.catalystWrite.isSome → c.catalystHead < c.catalyst.length)
    then some _ else none) = some d at step
  by_cases legal : a.inputMove.apply c.inputHead ≤ input.length + 1 ∧
    a.catalystMove.apply c.catalystHead ≤ c.catalyst.length ∧
    (a.catalystWrite.isSome → c.catalystHead < c.catalyst.length)
  · rw [if_pos legal] at step
    cases step
    simp only [Machine.step, embed, machine, Equiv.symm_apply_apply, state, liftInstruction]
    change (if a.inputMove.apply c.inputHead ≤ input.length + 1 ∧
        a.catalystMove.apply c.catalystHead ≤ c.catalyst.length ∧
        (a.catalystWrite.isSome → c.catalystHead < c.catalyst.length)
      then some _ else none) = some _
    rw [if_pos legal]
  · rw [if_neg legal] at step
    contradiction

theorem prefix_run (A : Machine) (tags : ℕ) (tag : Fin (tags + 1)) (input : List Bool)
    (I : ℕ → Configuration A → Prop) (c d : Configuration A) (T : ℕ)
    (H : FirstExit (A.step input) I {e | e.state = none} c d T) :
    ∀ u ≤ T, ∀ e, runFrom (A.step input) c u = some e →
      runFrom ((machine A tags).step input) (embed A tags tag c) u = some (embed A tags tag e) := by
  intro u
  induction u with
  | zero =>
      intro _ e he
      have equal : c = e := by simpa only [runFrom_zero, Option.some.injEq] using he
      subst e
      rfl
  | succ u ih =>
      intro hu e he
      obtain ⟨before, hb, _⟩ := H.toSegment.at (show u ≤ T by omega)
      have last : A.step input before = some e := by
        simpa only [runFrom_succ, hb, Option.bind_some] using he
      have live : before.state ≠ none := H.cut u (by omega) before hb
      obtain ⟨q, state⟩ := Option.ne_none_iff_exists'.mp live
      rw [runFrom_succ, ih (by omega) before hb, Option.bind_some]
      exact step_live A tags tag input before e q state last

/-- A finite context survives every physical child step and is available at
the live return port. This adds no work cells and no uncharged child transition. -/
theorem firstExit (A : Machine) (tags : ℕ) (tag : Fin (tags + 1)) (input : List Bool)
    (I : ℕ → Configuration A → Prop)
    (J : ℕ → Configuration (machine A tags) → Prop)
    (c d : Configuration A) (T : ℕ)
    (H : FirstExit (A.step input) I {e | e.state = none} c d T)
    (lift : ∀ u ≤ T, ∀ e, I u e → J u (embed A tags tag e)) :
    FirstExit ((machine A tags).step input) J
      {e | e.state = some (returned A tags tag)}
      (embed A tags tag c) (embed A tags tag d) T where
  result := prefix_run A tags tag input I c d T H T le_rfl d H.result
  during u hu e he := by
    obtain ⟨source, hs, inv⟩ := H.toSegment.at hu
    have native := prefix_run A tags tag input I c d T H u hu source hs
    have equal := Option.some.inj (native.symm.trans he)
    rw [← equal]
    exact lift u hu source inv
  exit_mem := by
    have halt : d.state = none := H.exit_mem
    simp only [Set.mem_setOf_eq, embed, halt, returned]
  cut u hu e he port := by
    obtain ⟨source, hs, _⟩ := H.toSegment.at (show u ≤ T by omega)
    have native := prefix_run A tags tag input I c d T H u (by omega) source hs
    have equal := Option.some.inj (native.symm.trans he)
    rw [← equal] at port
    change some (encode A tags (tag, source.state)) = some (encode A tags (tag, none)) at port
    have halted := congrArg Prod.snd ((encode A tags).injective (Option.some.inj port))
    exact H.cut u hu source hs halted

/-- Native child envelopes and writable footprints survive finite-context
retention unchanged, up to the explicitly live tagged return port. -/
theorem framed_firstExit (A : Machine) (tags : ℕ) (tag : Fin (tags + 1))
    (input : List Bool) (c d : Configuration A) (T : ℕ) (E : Envelope) (F : Footprint)
    (H : FirstExit (A.step input) (fun _ e => E.Contains e ∧ SameOutside F c e)
      {e | e.state = none} c d T) :
    FirstExit ((machine A tags).step input)
      (fun _ e => E.Contains e ∧ SameOutside F (embed A tags tag c) e)
      {e | e.state = some (returned A tags tag)}
      (embed A tags tag c) (embed A tags tag d) T := by
  apply firstExit A tags tag input _ _ c d T H
  intro u hu e inv
  simpa only [Envelope.Contains, SameOutside, embed] using inv

end CatalyticTreeEval.Contracts.TaggedReturn


open CatalyticMatching.General CatalyticTreeEval.Contracts CatalyticTreeEval.Contracts.TaggedReturn

theorem solution (A : Machine) (tags : ℕ) (tag : Fin (tags + 1))
    (input : List Bool) (c d : Configuration A) (T : ℕ) (E : Envelope) (F : Footprint)
    (H : FirstExit (A.step input) (fun _ e => E.Contains e ∧ SameOutside F c e)
      {e | e.state = none} c d T) :
    FirstExit ((machine A tags).step input)
      (fun _ e => E.Contains e ∧ SameOutside F (embed A tags tag c) e)
      {e | e.state = some (returned A tags tag)}
      (embed A tags tag c) (embed A tags tag d) T := by
  exact framed_firstExit A tags tag input c d T E F H
