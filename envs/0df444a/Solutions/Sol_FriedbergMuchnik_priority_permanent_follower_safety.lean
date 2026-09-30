-- Prove2me | solution 1 for FriedbergMuchnik.priority_permanent_follower_safety
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T22:54:01.060309+00:00
-- url     : https://prove2.me/submissions/c9f51127-5e0c-4f5b-9c7f-65fed94995b4

import Definitions.Def_FriedbergMuchnik_Priority

set_option autoImplicit false

open FriedbergMuchnik

private def selected (s : ℕ) : Option ℕ :=
  (List.range s).find? (wantsAttention s (priorityStage s))

private def entry (s q : ℕ) : ℕ × Bool :=
  (priorityStage s).2[q]?.getD (0, false)

private theorem entries_length (s : ℕ) : (priorityStage s).2.length = s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      simp only [priorityStage, priorityStep]
      split <;> simp [ih]

private theorem entry_next (s q : ℕ) (hq : q < s) :
    entry (s + 1) q =
      match selected s with
      | none => entry s q
      | some p => if p < q then (Nat.pair q (s + 1), false)
          else if q = p then ((entry s q).1, true) else entry s q := by
  have hb : q < (priorityStage s).2.length := by simpa [entries_length] using hq
  cases hs : selected s with
  | none =>
      change (List.range s).find? (wantsAttention s (priorityStage s)) = none at hs
      simp only [entry, priorityStage, priorityStep, hs, List.getElem?_append_left hb]
  | some p =>
      have hm : q < ((priorityStage s).2.mapIdx fun k e =>
          if p < k then (Nat.pair k (s + 1), false)
          else if k = p then (e.1, true) else e).length := by simpa using hb
      change (List.range s).find? (wantsAttention s (priorityStage s)) = some p at hs
      simp only [entry, priorityStage, priorityStep, hs]
      rw [List.getElem?_append_left hm, List.getElem?_mapIdx,
        List.getElem?_eq_getElem hb]
      simp only [Option.map_some, Option.getD_some]

private theorem selected_info {s p : ℕ} (h : selected s = some p) :
    p < s ∧ wantsAttention s (priorityStage s) p = true ∧
      (entry s p).2 = false := by
  have hm := List.mem_of_find?_eq_some h
  have ht := List.find?_some h
  refine ⟨by simpa using hm, ht, ?_⟩
  have ht' := ht
  change ((! (entry s p).2) && _) = true at ht'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht'
  exact ht'.1

private theorem entry_new (s : ℕ) :
    entry (s + 1) s = (Nat.pair s (s + 1), false) := by
  simp only [entry, priorityStage, priorityStep]
  split <;> rw [List.getElem?_append_right (by simp [entries_length])] <;>
    simp [entries_length]

/-- Each follower records its owning requirement and an appointment stage. -/
private theorem entry_code (s q : ℕ) (hq : q < s) :
    (entry s q).1.unpair.1 = q ∧
      q < (entry s q).1.unpair.2 ∧ (entry s q).1.unpair.2 ≤ s := by
  induction s generalizing q with
  | zero => omega
  | succ s ih =>
      by_cases heq : q = s
      · subst q
        simp [entry_new, Nat.unpair_pair]
      · have hqs : q < s := by omega
        have hi := ih q hqs
        rw [entry_next s q hqs]
        cases hp : selected s with
        | none => exact ⟨hi.1, hi.2.1, hi.2.2.trans (Nat.le_succ s)⟩
        | some p =>
            by_cases hpq : p < q
            · simp [hpq, Nat.unpair_pair]
              omega
            · simp only [hpq, ↓reduceIte]
              split <;> exact ⟨hi.1, hi.2.1, hi.2.2.trans (Nat.le_succ s)⟩

private theorem entry_birth_mono (q s t : ℕ) (hq : q < s) (hst : s ≤ t) :
    (entry s q).1.unpair.2 ≤ (entry t q).1.unpair.2 := by
  induction t, hst using Nat.le_induction with
  | base => exact le_refl _
  | succ t ht ih =>
      have hqt : q < t := by omega
      have hb := (entry_code t q hqt).2.2
      rw [entry_next t q hqt]
      cases hp : selected t with
      | none => exact ih
      | some p =>
          by_cases hpq : p < q
          · simp only [hpq, ↓reduceIte, Nat.unpair_pair]
            omega
          · simp only [hpq, ↓reduceIte]
            split <;> exact ih

private theorem stageList_next (i : Bool) (s n : ℕ) :
    n ∈ stageList i (s + 1) ↔ n ∈ stageList i s ∨
      ∃ p, selected s = some p ∧ side p = !i ∧ (entry s p).1 = n := by
  cases hs : selected s with
  | none =>
      change (List.range s).find? (wantsAttention s (priorityStage s)) = none at hs
      simp [stageList, priorityStage, priorityStep, hs, stateList]
  | some p =>
      have hs' : (List.range s).find? (wantsAttention s (priorityStage s)) = some p := hs
      simp only [stageList, priorityStage, priorityStep, hs', Option.some.injEq, stateList]
      cases i <;> cases hp : side p <;> simp [hp, entry, eq_comm, or_comm]

private theorem stageList_mono (i : Bool) {s t : ℕ} (hst : s ≤ t)
    {n : ℕ} (hn : n ∈ stageList i s) : n ∈ stageList i t := by
  induction t, hst using Nat.le_induction with
  | base => exact hn
  | succ t _ ih => exact (stageList_next i t n).mpr (Or.inl ih)

/-- Enumerated numbers have appointment stages earlier than the current stage. -/
private theorem mem_birth_lt (i : Bool) (s n : ℕ) (hn : n ∈ stageList i s) :
    n.unpair.2 < s := by
  induction s with
  | zero => simp [stageList, priorityStage, stateList] at hn
  | succ s ih =>
      rcases (stageList_next i s n).mp hn with hold | ⟨p, hp, _, rfl⟩
      · exact (ih hold).trans_le (Nat.le_succ s)
      · have hps := (selected_info hp).1
        exact Nat.lt_succ_of_le (entry_code s p hps).2.2

private theorem fresh_not_mem (i : Bool) (s q : ℕ) :
    Nat.pair q s ∉ stageList i s := by
  intro h
  have hb := mem_birth_lt i s (Nat.pair q s) h
  simp only [Nat.unpair_pair, Nat.lt_irrefl] at hb

private theorem distinct_followers (s p q : ℕ) (hp : p < s) (hq : q < s)
    (hpq : p ≠ q) : (entry s p).1 ≠ (entry s q).1 := by
  intro h
  have he := congrArg (fun n : ℕ => n.unpair.1) h
  rw [(entry_code s p hp).1, (entry_code s q hq).1] at he
  exact hpq he

/-- At each finite stage, a current follower has been enumerated on the
opposite side exactly when its current acted flag is true. -/
private theorem entry_membership (s q : ℕ) (hq : q < s) :
    (entry s q).1 ∈ stageList (!(side q)) s ↔ (entry s q).2 = true := by
  induction s generalizing q with
  | zero => omega
  | succ s ih =>
      by_cases heq : q = s
      · subst q
        rw [entry_new]
        simp [fresh_not_mem]
      · have hqs : q < s := by omega
        cases hs : selected s with
        | none =>
            have he : entry (s + 1) q = entry s q := by rw [entry_next s q hqs, hs]
            rw [he, stageList_next]
            simpa [hs] using ih q hqs
        | some p =>
            by_cases hpq : p < q
            · have he : entry (s + 1) q = (Nat.pair q (s + 1), false) := by
                rw [entry_next s q hqs, hs]
                simp [hpq]
              rw [he]
              simp [fresh_not_mem]
            · by_cases hqp : q = p
              · subst p
                have he : entry (s + 1) q = ((entry s q).1, true) := by
                  rw [entry_next s q hqs, hs]
                  simp
                rw [he]
                refine ⟨fun _ => rfl, fun _ => ?_⟩
                exact (stageList_next (!(side q)) s _).mpr
                  (Or.inr ⟨q, hs, by simp, rfl⟩)
              · have he : entry (s + 1) q = entry s q := by
                  rw [entry_next s q hqs, hs]
                  simp [hpq, hqp]
                have hneq := distinct_followers s p q (selected_info hs).1 hqs (Ne.symm hqp)
                rw [he, stageList_next]
                simpa [hs, hneq] using ih q hqs

/-- An acted flag is supported by an earlier selection of the same follower. -/
private theorem acted_history (s q : ℕ) (hq : q < s) (hb : (entry s q).2 = true) :
    ∃ t, t < s ∧ selected t = some q ∧ (entry t q).1 = (entry s q).1 := by
  induction s generalizing q with
  | zero => omega
  | succ s ih =>
      by_cases heq : q = s
      · subst q
        simp [entry_new] at hb
      · have hqs : q < s := by omega
        cases hs : selected s with
        | none =>
            have he : entry (s + 1) q = entry s q := by rw [entry_next s q hqs, hs]
            rw [he] at hb ⊢
            obtain ⟨t, ht, hsel, hx⟩ := ih q hqs hb
            exact ⟨t, by omega, hsel, hx⟩
        | some p =>
            by_cases hpq : p < q
            · have he : entry (s + 1) q = (Nat.pair q (s + 1), false) := by
                rw [entry_next s q hqs, hs]
                simp [hpq]
              simp [he] at hb
            · by_cases hqp : q = p
              · subst p
                refine ⟨s, by omega, hs, ?_⟩
                rw [entry_next s q hqs, hs]
                simp
              · have he : entry (s + 1) q = entry s q := by
                  rw [entry_next s q hqs, hs]
                  simp [hpq, hqp]
                rw [he] at hb ⊢
                obtain ⟨t, ht, hsel, hx⟩ := ih q hqs hb
                exact ⟨t, by omega, hsel, hx⟩

private theorem selected_zero {t q : ℕ} (hsel : selected t = some q) :
    oracleEvaln (stateOracle (priorityStage t) (side q)) t
      (Denumerable.ofNat Program (q / 2)) (entry t q).1 = some 0 := by
  have ht := (selected_info hsel).2.1
  change ((! (entry t q).2) && _) = true at ht
  simp only [Bool.and_eq_true] at ht
  simpa only [beq_iff_eq, entry] using ht.2

/-- A later higher priority action would irreversibly increase the permanent
follower's appointment stage, contradicting its earlier value. -/
private theorem no_higher_after {q t a x : ℕ} {b : Bool}
    (hqt : q < t) (hx : (entry t q).1 = x)
    (hstable : ∀ s, a ≤ s → entry s q = (x, b)) :
    ∀ s, t ≤ s → ∀ p, p < q → selected s ≠ some p := by
  intro s hs p hp hsel
  have hqs : q < s := by omega
  have hreset : entry (s + 1) q = (Nat.pair q (s + 1), false) := by
    rw [entry_next s q hqs, hsel]
    simp [hp]
  have hxbound : x.unpair.2 ≤ t := by
    rw [← hx]
    exact (entry_code t q hqt).2.2
  have hm := entry_birth_mono q (s + 1) (max a (s + 1)) (by omega) (le_max_right _ _)
  rw [hreset, hstable _ (le_max_left _ _), Nat.unpair_pair] at hm
  change s + 1 ≤ x.unpair.2 at hm
  omega

/-- Lower priority followers are above the protected use after the action. -/
private theorem lower_follower_bound {t q s p : ℕ}
    (hsel : selected t = some q) (hts : t < s) (hqp : q < p) (hps : p < s) :
    t < (entry s p).1 := by
  have hb : t < (entry s p).1.unpair.2 := by
    by_cases hpt : p ≤ t
    · have hstart : (entry (t + 1) p).1.unpair.2 = t + 1 := by
        by_cases heq : p = t
        · subst p
          simp [entry_new, Nat.unpair_pair]
        · rw [entry_next t p (by omega), hsel]
          simp [hqp, Nat.unpair_pair]
      have hm := entry_birth_mono p (t + 1) s (by omega) (by omega)
      rw [hstart] at hm
      omega
    · have hi := (entry_code s p hps).2.1
      omega
  exact hb.trans_le (Nat.unpair_right_le _)

private theorem oracle_prefix_frozen {q t : ℕ} (hsel : selected t = some q)
    (hno : ∀ s, t ≤ s → ∀ p, p < q → selected s ≠ some p) :
    ∀ s, t ≤ s → ∀ n, n < t →
      (n ∈ stageList (side q) s ↔ n ∈ stageList (side q) t) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact fun _ _ => Iff.rfl
  | succ s hs ih =>
      intro n hn
      constructor
      · intro hmem
        rcases (stageList_next (side q) s n).mp hmem with hold | ⟨p, hp, hside, hx⟩
        · exact (ih n hn).mp hold
        · by_cases hpq : p < q
          · exact False.elim (hno s hs p hpq hp)
          · by_cases heq : p = q
            · subst p
              cases hsideq : side q <;> simp [hsideq] at hside
            · have hts : t < s := by
                by_contra h
                have heq : s = t := by omega
                subst s
                have hqp := Option.some.inj (hsel.symm.trans hp)
                omega
              have hlarge := lower_follower_bound hsel hts (by omega : q < p) (selected_info hp).1
              rw [hx] at hlarge
              omega
      · intro hmem
        exact (stageList_next (side q) s n).mpr (Or.inl ((ih n hn).mpr hmem))

theorem solution (q a x : ℕ) (b : Bool)
    (hqa : q < a)
    (hstable : ∀ s : ℕ, a ≤ s →
      (priorityStage s).2[q]?.getD (0, false) = (x, b)) :
    (x ∈ limitSet (!(side q)) ↔ b = true) ∧
    (b = true → ∃ t : ℕ, t < a ∧
      oracleEvaln (stateOracle (priorityStage t) (side q)) t
        (Denumerable.ofNat Program (q / 2)) x = some 0 ∧
      ∀ n : ℕ, n < t →
        (n ∈ stageList (side q) t ↔ n ∈ limitSet (side q))) := by
  have hentry : ∀ s, a ≤ s → entry s q = (x, b) := hstable
  have ha := hentry a (le_refl a)
  constructor
  · constructor
    · rintro ⟨s, hs⟩
      have hmem := stageList_mono (!(side q)) (le_max_right a s) hs
      have hiff := entry_membership (max a s) q (by omega)
      rw [hentry _ (le_max_left _ _)] at hiff
      exact hiff.mp hmem
    · intro hb
      have hiff := entry_membership a q hqa
      rw [ha] at hiff
      exact ⟨a, hiff.mpr hb⟩
  · intro hb
    have hba : (entry a q).2 = true := by rw [ha]; exact hb
    obtain ⟨t, hta, hsel, hx⟩ := acted_history a q hqa hba
    have htx : (entry t q).1 = x := hx.trans (congrArg Prod.fst ha)
    have hzero := selected_zero hsel
    rw [htx] at hzero
    have hno := no_higher_after (selected_info hsel).1 htx hentry
    have hfrozen := oracle_prefix_frozen hsel hno
    refine ⟨t, hta, hzero, ?_⟩
    intro n hn
    constructor
    · intro hm
      exact ⟨t, hm⟩
    · rintro ⟨s, hs⟩
      have hm := stageList_mono (side q) (le_max_left s t) hs
      exact (hfrozen (max s t) (le_max_right _ _) n hn).mp hm
