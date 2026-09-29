-- Prove2me | solution 1 for Freiman.lowerHistory_source_dnf_induction
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-11T02:25:07.155062+00:00
-- url     : https://prove2.me/submissions/04a0a7d6-249f-4c5a-afb7-65c35daa5249

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option autoImplicit false

private def av_loop (row : ℕ) : List (LowerLabel × Bool) → LowerPair →
    LowerHistoryState → List (List CertBound) → List (List CertBound)
  | [], words, s, alternatives =>
    match lowerHistoryNecessary s words with
    | none => []
    | some good => alternatives.map fun cs =>
        (cs ++ good ++ (lowerHistoryFinalCuts row).map
          (fun b => lowerHistoryPull b words s.wider)).eraseDups
  | (l,reflect)::tail, words, s, alternatives =>
    match lowerHistoryNecessary s words with
    | none => []
    | some good =>
      let nextWords := lowerHistoryRawStep words s.wider l
      let nextState := lowerHistoryAdvance s l reflect
      let forced := decide (l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])])
      av_loop row tail nextWords nextState
        ((alternatives.flatMap fun cs =>
          (lowerHistorySourceChoices s l).map fun ch =>
            cs ++ good ++ ch.map (fun b => lowerHistoryPull b words s.wider)).map
          fun cs => cs ++ [lowerHistoryNormalization nextWords nextState.wider forced])

private def av_program (row : ℕ) (steps : List (LowerLabel × Bool))
    (initialWords : LowerPair) (initialState : LowerHistoryState)
    (initialAlternatives : List (List CertBound)) : List (List CertBound) := Id.run do
  let mut alternatives := initialAlternatives
  let mut words := initialWords
  let mut s := initialState
  for (l,reflect) in steps do
    match lowerHistoryNecessary s words with
    | none => return []
    | some good =>
      alternatives := alternatives.flatMap fun cs =>
        (lowerHistorySourceChoices s l).map fun ch =>
          cs ++ good ++ ch.map (fun b => lowerHistoryPull b words s.wider)
    words := lowerHistoryRawStep words s.wider l
    s := lowerHistoryAdvance s l reflect
    let forced := decide (l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])])
    alternatives := alternatives.map fun cs =>
      cs ++ [lowerHistoryNormalization words s.wider forced]
  match lowerHistoryNecessary s words with
  | none => return []
  | some good =>
    let final := good ++ (lowerHistoryFinalCuts row).map
      (fun b => lowerHistoryPull b words s.wider)
    return alternatives.map fun cs => (cs ++ final).eraseDups

private theorem av_program_eq (row : ℕ) (steps : List (LowerLabel × Bool))
    (words : LowerPair) (s : LowerHistoryState) (alternatives : List (List CertBound)) :
    av_program row steps words s alternatives = av_loop row steps words s alternatives := by
  induction steps generalizing words s alternatives with
  | nil =>
    cases hg : lowerHistoryNecessary s words <;>
      simp [av_program, av_loop, hg, Id.run, List.append_assoc] <;> rfl
  | cons step tail ih =>
    rcases step with ⟨l,reflect⟩
    cases hg : lowerHistoryNecessary s words with
    | none => simp [av_program, av_loop, List.forIn_cons, hg]
    | some good =>
      simpa [av_program, av_loop, List.forIn_cons, hg, List.append_assoc] using
        ih (lowerHistoryRawStep words s.wider l) (lowerHistoryAdvance s l reflect)
          ((alternatives.flatMap fun cs =>
            (lowerHistorySourceChoices s l).map fun ch =>
              cs ++ good ++ ch.map (fun b => lowerHistoryPull b words s.wider)).map
            fun cs => cs ++ [lowerHistoryNormalization
              (lowerHistoryRawStep words s.wider l) (lowerHistoryAdvance s l reflect).wider
              (decide (l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]))])

private theorem av_source_eq (p : LowerHistoryPath) (bs : List CertBound)
    (hb : lowerHistoryBasePremises p = some bs) :
    lowerHistorySourcePremises p =
      av_loop p.row p.steps (lowerHistoryRawStep ([],[]) false p.entry)
        (lowerHistoryInitialState p)
        [bs ++ [lowerHistoryNormalization (lowerHistoryRawStep ([],[]) false p.entry)
          (lowerHistoryInitialState p).wider false]] := by
  rw [← av_program_eq]
  by_cases hc : p.catalog = .initial
  · simp only [lowerHistoryBasePremises, hc, if_true, Option.some.injEq] at hb
    subst bs
    simp [lowerHistorySourcePremises, av_program, hc, Id.run] <;> rfl
  · cases hg : lowerHistoryRelaxedGoodness ⟨(p.context,[3,1]),(false,false)⟩ with
    | none => simp [lowerHistoryBasePremises, hc, hg] at hb
    | some good =>
      simp only [lowerHistoryBasePremises, hc, if_false, hg, Option.map_some,
        Option.some.injEq] at hb
      subst bs
      simp [lowerHistorySourcePremises, av_program, hc, hg, Id.run] <;> rfl

private theorem av_at_append (base : LowerPair) {xs ys : List CertBound}
    (hx : lowerHistoryAtBase base xs) (hy : lowerHistoryAtBase base ys) :
    lowerHistoryAtBase base (xs ++ ys) := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hx b hb
  · exact hy b hb

private theorem av_at_eraseDups (base : LowerPair) {xs : List CertBound}
    (hx : lowerHistoryAtBase base xs) : lowerHistoryAtBase base xs.eraseDups := by
  intro b hb
  exact hx b (List.mem_eraseDups.mp hb)

private theorem av_advance_wider (s : LowerHistoryState) (l : LowerLabel) (r : Bool) :
    (lowerHistoryAdvance s l r).wider = if r then !s.wider else s.wider := by
  cases hw : s.wider <;> cases r <;> simp [lowerHistoryAdvance, hw]

private theorem av_fold_wider (steps : List (LowerLabel × Bool))
    (words : LowerPair) (s : LowerHistoryState) :
    (steps.foldl (fun a step =>
      (lowerHistoryRawStep a.1 a.2 step.1, if step.2 then !a.2 else a.2))
      (words,s.wider)).2 =
    (steps.foldl (fun a step => lowerHistoryAdvance a step.1 step.2) s).wider := by
  induction steps generalizing words s with
  | nil => rfl
  | cons step tail ih =>
    rcases step with ⟨l,r⟩
    simpa only [List.foldl_cons, av_advance_wider] using
      ih (lowerHistoryRawStep words s.wider l) (lowerHistoryAdvance s l r)

private theorem av_replay_wider (p : LowerHistoryPath) (j : ℕ) :
    (lowerHistoryReplay ([],[]) p j).2 = (lowerHistoryStateAt p j).wider := by
  have hwide : (lowerHistoryInitialState p).wider = p.initialWider := rfl
  simpa only [lowerHistoryReplay, lowerHistoryStateAt, hwide] using
    av_fold_wider (p.steps.take j) (lowerHistoryRawStep ([],[]) false p.entry)
      (lowerHistoryInitialState p)

private theorem av_state_succ (p : LowerHistoryPath) (j : ℕ) (l : LowerLabel) (r : Bool)
    (h : p.steps[j]? = some (l,r)) :
    lowerHistoryStateAt p (j+1) = lowerHistoryAdvance (lowerHistoryStateAt p j) l r := by
  simp [lowerHistoryStateAt, List.take_add_one, h, List.foldl_append]

private theorem av_words_succ (p : LowerHistoryPath) (j : ℕ) (l : LowerLabel) (r : Bool)
    (h : p.steps[j]? = some (l,r)) :
    lowerHistoryWordsAt p (j+1) = lowerHistoryRawStep
      (lowerHistoryWordsAt p j) (lowerHistoryStateAt p j).wider l := by
  have hr : lowerHistoryReplay ([],[]) p (j+1) =
      (lowerHistoryRawStep (lowerHistoryReplay ([],[]) p j).1
        (lowerHistoryReplay ([],[]) p j).2 l,
        if r then !(lowerHistoryReplay ([],[]) p j).2
        else (lowerHistoryReplay ([],[]) p j).2) := by
    simp [lowerHistoryReplay, List.take_add_one, h, List.foldl_append]
  simpa only [lowerHistoryWordsAt, av_replay_wider] using congrArg Prod.fst hr

private theorem av_drop_head {α : Type} (xs : List α) (j : ℕ) (a : α) (tail : List α)
    (h : xs.drop j = a::tail) : xs[j]? = some a := by
  induction j generalizing xs with
  | zero =>
    have hx : xs = a :: tail := by simpa only [List.drop_zero] using h
    subst xs
    rfl
  | succ j ih =>
    cases xs with
    | nil => simp at h
    | cons x xs => exact ih xs h

private theorem av_loop_satisfied (base : LowerPair) (p : LowerHistoryPath)
    (hp : lowerHistoryStructural p) (he : LowerHistorySourceEvents base p)
    (tail : List (LowerLabel × Bool)) (j : ℕ)
    (hj : j ≤ p.steps.length) (htail : p.steps.drop j = tail)
    (alternatives : List (List CertBound))
    (ha : ∃ cs ∈ alternatives, lowerHistoryAtBase base cs) :
    ∃ cs ∈ av_loop p.row tail (lowerHistoryWordsAt p j)
      (lowerHistoryStateAt p j) alternatives, lowerHistoryAtBase base cs := by
  induction tail generalizing j alternatives with
  | nil =>
    have hj' : j = p.steps.length :=
      Nat.le_antisymm hj (List.drop_eq_nil_iff.mp htail)
    subst j
    obtain ⟨good,hgood,hgoodAt⟩ := he.goodEvents p.steps.length (Nat.le_refl _)
    have hw : (lowerHistoryStateAt p p.steps.length).wider = p.finalWider := by
      simpa only [lowerHistoryStateAt, List.take_length, lowerHistoryFinalState] using
        hp.2.2.2.1.2.2.2
    have hfinal : lowerHistoryAtBase base ((lowerHistoryFinalCuts p.row).map
        (fun b => lowerHistoryPull b (lowerHistoryWordsAt p p.steps.length)
          (lowerHistoryStateAt p p.steps.length).wider)) := by
      simpa only [lowerHistoryFinalEvent, hw] using he.finalEvent
    obtain ⟨cs,hcs,hcsAt⟩ := ha
    refine ⟨(cs ++ good ++ (lowerHistoryFinalCuts p.row).map
      (fun b => lowerHistoryPull b (lowerHistoryWordsAt p p.steps.length)
        (lowerHistoryStateAt p p.steps.length).wider)).eraseDups, ?_,
      av_at_eraseDups base (av_at_append base (av_at_append base hcsAt hgoodAt) hfinal)⟩
    simp only [av_loop, hgood]
    exact List.mem_map.mpr ⟨cs,hcs,rfl⟩
  | cons step tail ih =>
    rcases step with ⟨l,r⟩
    have hindex : p.steps[j]? = some (l,r) := av_drop_head p.steps j (l,r) tail htail
    obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hindex
    have hnext : p.steps.drop (j+1) = tail := by
      rw [List.drop_add_one_eq_tail_drop, htail]
      rfl
    obtain ⟨good,hgood,hgoodAt⟩ := he.goodEvents j hj
    obtain ⟨choice,hchoice,hchoiceAt⟩ := he.choiceEvents j l r hindex
    obtain ⟨cs,hcs,hcsAt⟩ := ha
    let nextAlternatives :=
      ((alternatives.flatMap fun cs =>
        (lowerHistorySourceChoices (lowerHistoryStateAt p j) l).map fun ch =>
          cs ++ good ++ ch.map (fun b => lowerHistoryPull b
            (lowerHistoryWordsAt p j) (lowerHistoryStateAt p j).wider)).map
        fun cs => cs ++ [lowerHistoryNormalization (lowerHistoryWordsAt p (j+1))
          (lowerHistoryStateAt p (j+1)).wider
          (decide (l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]))])
    have hnorm : lowerHistoryAtBase base [lowerHistoryNormalization
        (lowerHistoryWordsAt p (j+1)) (lowerHistoryStateAt p (j+1)).wider
        (decide (l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]))] := by
      have hn := he.normalizationEvents (j+1) (by omega)
      simpa [Nat.add_sub_cancel, hindex] using hn
    have hnextAt : ∃ bs ∈ nextAlternatives, lowerHistoryAtBase base bs := by
      refine ⟨(cs ++ good ++ choice.map (fun b => lowerHistoryPull b
        (lowerHistoryWordsAt p j) (lowerHistoryStateAt p j).wider)) ++
          [lowerHistoryNormalization (lowerHistoryWordsAt p (j+1))
            (lowerHistoryStateAt p (j+1)).wider
            (decide (l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]))], ?_,
        av_at_append base (av_at_append base (av_at_append base hcsAt hgoodAt) hchoiceAt) hnorm⟩
      apply List.mem_map.mpr
      refine ⟨_, ?_, rfl⟩
      apply List.mem_flatMap.mpr
      refine ⟨cs,hcs,?_⟩
      exact List.mem_map.mpr ⟨choice,hchoice,rfl⟩
    have hout := ih (j+1) (by omega) hnext nextAlternatives hnextAt
    simpa only [av_loop, hgood, nextAlternatives,
      av_words_succ p j l r hindex, av_state_succ p j l r hindex] using hout

theorem solution (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p)
    (he : LowerHistorySourceEvents base p) :
    ∃ bs ∈ lowerHistorySourcePremises p, lowerHistoryAtBase base bs := by
  obtain ⟨bs,hbs,hbsAt⟩ := he.baseEvent
  have hnorm : lowerHistoryAtBase base [lowerHistoryNormalization
      (lowerHistoryRawStep ([],[]) false p.entry) (lowerHistoryInitialState p).wider false] := by
    have h := he.normalizationEvents 0 (Nat.zero_le _)
    simpa [lowerHistoryWordsAt, lowerHistoryReplay, lowerHistoryStateAt] using h
  rw [av_source_eq p bs hbs]
  have hout := av_loop_satisfied base p hp he p.steps 0 (Nat.zero_le _) (by simp)
    [bs ++ [lowerHistoryNormalization (lowerHistoryRawStep ([],[]) false p.entry)
      (lowerHistoryInitialState p).wider false]]
    ⟨_, List.mem_singleton_self _, av_at_append base hbsAt hnorm⟩
  simpa only [lowerHistoryWordsAt, lowerHistoryReplay, lowerHistoryStateAt,
    List.take_zero, List.foldl_nil] using hout

#print axioms solution
