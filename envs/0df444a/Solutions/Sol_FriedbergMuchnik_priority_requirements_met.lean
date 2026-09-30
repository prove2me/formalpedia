-- Prove2me | solution 1 for FriedbergMuchnik.priority_requirements_met
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T21:55:48.046614+00:00
-- url     : https://prove2.me/submissions/ff1cc0ec-5873-4f84-9e9b-0a87996495bf

import Definitions.Def_FriedbergMuchnik_Priority
import Theorems.Thm_FriedbergMuchnik_priority_eventually_quiescent
import Theorems.Thm_FriedbergMuchnik_oracleEvaln_total_correct
import Theorems.Thm_FriedbergMuchnik_priority_permanent_follower_safety

set_option autoImplicit false

open FriedbergMuchnik

private theorem bind_extension {a b : Option ℕ} {f g : ℕ → Option ℕ}
    (ha : ∀ v, a = some v → b = some v)
    (hf : ∀ n v, f n = some v → g n = some v)
    {y : ℕ} (h : a.bind f = some y) : b.bind g = some y := by
  obtain ⟨v, hv, hy⟩ := Option.bind_eq_some_iff.mp h
  exact Option.bind_eq_some_iff.mpr ⟨v, ha v hv, hf v y hy⟩

private theorem boundedMu_extension {f g : ℕ → Option ℕ}
    (hfg : ∀ n v, f n = some v → g n = some v)
    {k r n y : ℕ} (hkr : k ≤ r) (h : boundedMu f k n = some y) :
    boundedMu g r n = some y := by
  induction k generalizing r n y with
  | zero => simp [boundedMu] at h
  | succ k ih =>
      cases r with
      | zero => omega
      | succ r =>
          simp only [boundedMu] at h ⊢
          apply bind_extension (fun v hv => hfg n v hv) _ h
          intro v z hv
          by_cases hz : v = 0
          · simpa [hz] using hv
          · simp only [hz, ↓reduceIte] at hv ⊢
            exact ih (r := r) (by omega) hv

/-- A successful bounded computation survives more fuel and any change to the
oracle above the original fuel bound. -/
private theorem oracleEvaln_extension {k r : ℕ} {O O' : ℕ → ℕ}
    (hkr : k ≤ r) (hO : ∀ n, n < k → O' n = O n)
    (c : Program) (x y : ℕ) (h : oracleEvaln O k c x = some y) :
    oracleEvaln O' r c x = some y := by
  induction k generalizing r O O' c x y with
  | zero => simp [oracleEvaln] at h
  | succ k ih =>
      cases r with
      | zero => omega
      | succ r =>
          have hx : x < k + 1 := by
            by_contra hn
            simp [oracleEvaln, hn] at h
          have hx' : x < r + 1 := by omega
          have hm : ∀ d n v, oracleEvaln O k d n = some v →
              oracleEvaln O' r d n = some v :=
            fun d n v hv => ih (by omega) (fun m hm => hO m (by omega)) d n v hv
          cases c with
          | query => simpa [oracleEvaln, hx, hx', hO x hx] using h
          | succ => simpa [oracleEvaln, hx, hx'] using h
          | left => simpa [oracleEvaln, hx, hx'] using h
          | right => simpa [oracleEvaln, hx, hx'] using h
          | pair f g =>
              simp only [oracleEvaln, hx, hx', ↓reduceIte] at h ⊢
              apply bind_extension (hm f x) _ h
              intro a v hv
              exact bind_extension (hm g x) (fun _ _ hh => hh) hv
          | comp f g =>
              simp only [oracleEvaln, hx, hx', ↓reduceIte] at h ⊢
              exact bind_extension (hm g x) (hm f) h
          | prec f g =>
              simp only [oracleEvaln, hx, hx', ↓reduceIte] at h ⊢
              have hrec : ∀ m v : ℕ,
                  (m.rec (oracleEvaln O k f x.unpair.1) fun j ih =>
                    ih.bind fun z => oracleEvaln O k g (Nat.pair x.unpair.1 (Nat.pair j z))) = some v →
                  (m.rec (oracleEvaln O' r f x.unpair.1) fun j ih =>
                    ih.bind fun z => oracleEvaln O' r g (Nat.pair x.unpair.1 (Nat.pair j z))) = some v := by
                intro m
                induction m with
                | zero => exact hm f x.unpair.1
                | succ m ihm =>
                    intro v hv
                    exact bind_extension ihm (fun z => hm g (Nat.pair x.unpair.1 (Nat.pair m z))) hv
              exact hrec x.unpair.2 y h
          | mu f =>
              simp only [oracleEvaln, hx, hx', ↓reduceIte] at h ⊢
              exact boundedMu_extension (fun n => hm f (Nat.pair x n)) (by omega) h

private theorem stageList_step (i : Bool) (s : ℕ) :
    ∀ n, n ∈ stageList i s → n ∈ stageList i (s + 1) := by
  intro n hn
  cases hfind : (List.range s).find? (wantsAttention s (priorityStage s)) with
  | none => simpa only [stageList, priorityStage, priorityStep, hfind, stateList] using hn
  | some q =>
      simp only [stageList, priorityStage, priorityStep, hfind, stateList]
      cases i <;> cases hside : side q <;>
        simp_all [stageList, stateList]

private theorem stageList_mono (i : Bool) {s t : ℕ} (hst : s ≤ t) :
    ∀ n, n ∈ stageList i s → n ∈ stageList i t := by
  intro n hn
  induction t, hst using Nat.le_induction with
  | base => exact hn
  | succ t _ ih => exact stageList_step i t n ih

/-- Every fixed finite prefix of an increasing stage oracle eventually agrees
with the union oracle. No computable stabilization modulus is asserted. -/
private theorem stageOracle_prefix (i : Bool) (k : ℕ) :
    ∃ a, ∀ s, a ≤ s → ∀ n, n < k →
      (n ∈ stageList i s ↔ n ∈ limitSet i) := by
  classical
  induction k with
  | zero => exact ⟨0, by intros; omega⟩
  | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      by_cases hk : k ∈ limitSet i
      · obtain ⟨b, hb⟩ := hk
        refine ⟨max a b, ?_⟩
        intro s hs n hn
        by_cases hnk : n < k
        · exact ha s (by omega) n hnk
        · have hnk' : n = k := by omega
          subst n
          have hmem := stageList_mono i (show b ≤ s by omega) k hb
          exact ⟨fun _ => ⟨b, hb⟩, fun _ => hmem⟩
      · refine ⟨a, ?_⟩
        intro s hs n hn
        by_cases hnk : n < k
        · exact ha s hs n hnk
        · have hnk' : n = k := by omega
          subst n
          have hnot : k ∉ stageList i s := fun h => hk ⟨s, h⟩
          simp [hnot, hk]

/-- The final diagonal argument, separating finite injury, follower safety,
and the adequacy of bounded oracle simulation. -/
theorem solution (i : Bool) (c : Program) :
    ∃ x : ℕ,
      (x ∈ limitSet (!i) ∧
        0 ∈ oracleEval (Computability.setOracle (limitSet i)) c x) ∨
      (x ∉ limitSet (!i) ∧
        0 ∉ oracleEval (Computability.setOracle (limitSet i)) c x) := by
  classical
  let q := 2 * Encodable.encode c + if i then 1 else 0
  have hside : side q = i := by
    cases i <;> simp [q, side, Nat.add_mod]
  have hprog : Denumerable.ofNat Program (q / 2) = c := by
    have hd : q / 2 = Encodable.encode c := by
      cases i <;> simp only [q, Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [hd]
    exact Denumerable.ofNat_encode c
  obtain ⟨a, hqa, hquiet⟩ := priority_eventually_quiescent q
  obtain ⟨x, b, hab⟩ : ∃ x b, (priorityStage a).2[q]?.getD (0, false) = (x, b) :=
    ⟨_, _, rfl⟩
  have hstable : ∀ s, a ≤ s → (priorityStage s).2[q]?.getD (0, false) = (x, b) :=
    fun s hs => (hquiet s hs).1.trans hab
  obtain ⟨hmem, hprotect⟩ := priority_permanent_follower_safety q a x b hqa hstable
  simp only [hside, hprog] at hmem hprotect
  let O : ℕ → ℕ := fun n => if n ∈ limitSet i then 1 else 0
  have hOracle : Computability.setOracle (limitSet i) = PFun.lift O := rfl
  refine ⟨x, ?_⟩
  cases hb : b with
  | false =>
      refine Or.inr ⟨?_, ?_⟩
      · intro hm
        have := hmem.mp hm
        simp [hb] at this
      · intro hz
        rw [hOracle] at hz
        obtain ⟨k, hk⟩ := (oracleEvaln_total_correct O c x 0).mp hz
        obtain ⟨d, hd⟩ := stageOracle_prefix i k
        let s := max a (max d k)
        have has : a ≤ s := le_max_left _ _
        have hds : d ≤ s := (le_max_left _ _).trans (le_max_right _ _)
        have hks : k ≤ s := (le_max_right _ _).trans (le_max_right _ _)
        have hsim : oracleEvaln (stateOracle (priorityStage s) i) s c x = some 0 := by
          apply oracleEvaln_extension hks _ c x 0 hk
          intro n hn
          change (if n ∈ stageList i s then 1 else 0) = _
          simp only [O, hd s hds n hn]
        have hatt := (hquiet s has).2 q (le_refl q)
        simp only [wantsAttention, hstable s has, hb, hside, hprog, hsim] at hatt
        contradiction
  | true =>
      refine Or.inl ⟨hmem.mpr hb, ?_⟩
      obtain ⟨t, _, ht, hpref⟩ := hprotect hb
      rw [hOracle]
      apply (oracleEvaln_total_correct O c x 0).mpr
      refine ⟨t, oracleEvaln_extension (le_refl t) ?_ c x 0 ht⟩
      intro n hn
      change (if n ∈ limitSet i then 1 else 0) =
        (if n ∈ stageList i t then 1 else 0)
      simp only [hpref n hn]
