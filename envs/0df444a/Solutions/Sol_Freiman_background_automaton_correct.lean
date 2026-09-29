-- Prove2me | solution 1 for Freiman.background_automaton_correct
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:21:35.1002+00:00
-- url     : https://prove2.me/submissions/3ab783d4-0d54-49d8-bd7a-76d83539e188

import Definitions.Def_Freiman_backgroundWords
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega
open Freiman
namespace BackgroundAutomatonSep10
private def shift (b : ℕ → ℕ+) : ℕ → ℕ+ := fun n => b (n+1)
private def Completion : BackgroundState → (ℕ → ℕ+) → Prop
  | .empty, _ => False
  | .three, b => (b 0:ℕ)=1 ∧ (b 1:ℕ)=3 ∧ (b 2:ℕ)=1 ∧ (b 3:ℕ)=3
  | .threeOne, b => (b 0:ℕ)=3 ∧ (b 1:ℕ)=1 ∧ (b 2:ℕ)=3
  | .threeOneThree, b => (b 0:ℕ)=1 ∧ (b 1:ℕ)=3
  | .threeOneThreeOne, b => (b 0:ℕ)=3
private def Safe (s : BackgroundState) (b : ℕ → ℕ+) : Prop :=
  OneSidedAvoidsBlock b [3,1,3,1,3] ∧ ¬ Completion s b

private theorem matches_five (b : ℕ → ℕ+) (i : ℕ) :
    OneSidedMatchesBlock b [3,1,3,1,3] i ↔
      (b i:ℕ)=3 ∧ (b (i+1):ℕ)=1 ∧ (b (i+2):ℕ)=3 ∧
      (b (i+3):ℕ)=1 ∧ (b (i+4):ℕ)=3 := by
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by decide), h 1 (by decide), h 2 (by decide),
      h 3 (by decide), h 4 (by decide)⟩
  · rintro ⟨h0,h1,h2,h3,h4⟩ k hk
    have hk' : k < 5 := hk
    interval_cases k <;> simp_all [List.getD]

private theorem matches_shift (b : ℕ → ℕ+) (w : List ℕ) (i : ℕ) :
    OneSidedMatchesBlock (shift b) w i ↔ OneSidedMatchesBlock b w (i+1) := by
  simp only [OneSidedMatchesBlock, shift, Nat.add_right_comm]

private theorem avoids_shift (b : ℕ → ℕ+) :
    OneSidedAvoidsBlock b [3,1,3,1,3] ↔
      ¬ OneSidedMatchesBlock b [3,1,3,1,3] 0 ∧
        OneSidedAvoidsBlock (shift b) [3,1,3,1,3] := by
  constructor
  · intro h
    exact ⟨h 0, fun i hi => h (i+1) ((matches_shift b _ i).mp hi)⟩
  · rintro ⟨h0,h⟩ i
    cases i with
    | zero => exact h0
    | succ i => exact fun hi => h i ((matches_shift b _ i).mpr hi)

private theorem safe_step (s : BackgroundState) (b : ℕ → ℕ+) :
    Safe s b ↔ ∃ t, backgroundStep s (b 0) = some t ∧ Safe t (shift b) := by
  unfold Safe
  rw [avoids_shift b, matches_five]
  cases s <;> by_cases h1 : (b 0:ℕ)=1 <;> by_cases h3 : (b 0:ℕ)=3 <;>
    simp [backgroundStep, Completion, h1, h3, shift] <;> tauto

private theorem run_cons (s : BackgroundState) (d : ℕ+) (w : List ℕ+) :
    backgroundRun s (d::w) = (backgroundStep s d).bind (fun t => backgroundRun t w) := by
  unfold backgroundRun
  simp only [List.foldl_cons, Option.bind_some]
  cases h : backgroundStep s d <;> simp [h]
  induction w with
  | nil => rfl
  | cons a w ih => simpa using ih

private theorem run_shift (s : BackgroundState) (b : ℕ → ℕ+) (n : ℕ) :
    backgroundRun s ((List.range (n+1)).map b) =
      (backgroundStep s (b 0)).bind (fun t => backgroundRun t ((List.range n).map (shift b))) := by
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, run_cons]
  rfl

private theorem safe_allowed (s : BackgroundState) (b : ℕ → ℕ+) (h : Safe s b) : BackgroundAllowed s b := by
  intro n
  induction n generalizing s b with
  | zero => simp [backgroundRun]
  | succ n ih =>
    obtain ⟨t,ht,hb⟩ := (safe_step s b).mp h
    rw [run_shift, ht]
    exact ih t (shift b) hb

private theorem run_append (s : BackgroundState) (u v : List ℕ+) :
    backgroundRun s (u++v) = (backgroundRun s u).bind (fun t => backgroundRun t v) := by
  unfold backgroundRun
  rw [List.foldl_append]
  cases h : u.foldl (fun q d => q.bind (fun t => backgroundStep t d)) (some s) <;> simp [h]
  induction v with
  | nil => rfl
  | cons a v ih => simpa using ih

private theorem allowed_safe (s : BackgroundState) (b : ℕ → ℕ+) (ha : BackgroundAllowed s b) : Safe s b := by
  constructor
  · intro i hm
    obtain ⟨h0,h1,h2,h3,h4⟩ := (matches_five b i).mp hm
    have p0 : b (i) = 3 := PNat.coe_injective h0
    have p1 : b (i+1) = 1 := PNat.coe_injective h1
    have p2 : b (i+2) = 3 := PNat.coe_injective h2
    have p3 : b (i+3) = 1 := PNat.coe_injective h3
    have p4 : b (i+4) = 3 := PNat.coe_injective h4
    cases hr : backgroundRun s ((List.range i).map b) with
    | none => exact ha i hr
    | some t =>
      have hend := ha (i+5)
      rw [List.range_add, List.map_append, run_append, hr] at hend
      simp only [Option.bind_some, List.map_map] at hend
      have hterm : backgroundRun t ((List.range 5).map (fun j => b (i+j))) = none := by
        cases t <;> norm_num [backgroundRun, List.range_succ, backgroundStep, p0,p1,p2,p3,p4]
      exact hend hterm
  · cases s
    · simp [Completion]
    · rintro ⟨h0,h1,h2,h3⟩
      have p0 : b 0 = 1 := PNat.coe_injective h0
      have p1 : b 1 = 3 := PNat.coe_injective h1
      have p2 : b 2 = 1 := PNat.coe_injective h2
      have p3 : b 3 = 3 := PNat.coe_injective h3
      have h := ha 4
      norm_num [backgroundRun, List.range_succ, backgroundStep, p0,p1,p2,p3] at h
    · rintro ⟨h0,h1,h2⟩
      have p0 : b 0 = 3 := PNat.coe_injective h0
      have p1 : b 1 = 1 := PNat.coe_injective h1
      have p2 : b 2 = 3 := PNat.coe_injective h2
      have h := ha 3
      norm_num [backgroundRun, List.range_succ, backgroundStep, p0,p1,p2] at h
    · rintro ⟨h0,h1⟩
      have p0 : b 0 = 1 := PNat.coe_injective h0
      have p1 : b 1 = 3 := PNat.coe_injective h1
      have h := ha 2
      norm_num [backgroundRun, List.range_succ, backgroundStep, p0,p1] at h
    · intro h0
      change (b 0:ℕ)=3 at h0
      have h := ha 1
      norm_num [backgroundRun, List.range_succ, backgroundStep, h0] at h

private theorem late_match (w : List ℕ+) (b : ℕ → ℕ+) (v : List ℕ) (i : ℕ) :
    OneSidedMatchesBlock (backgroundPrepend w b) v (w.length+i) ↔ OneSidedMatchesBlock b v i := by
  have heq (k : ℕ) : backgroundPrepend w b (w.length+i+k) = b (i+k) := by
    have hge : ¬ w.length+i+k < w.length := by omega
    have he : w.length+i+k-w.length = i+k := by omega
    simp [backgroundPrepend, hge, he]
  simp only [OneSidedMatchesBlock, heq]

private theorem avoids_prepend (w : List ℕ+) (b : ℕ → ℕ+) :
    OneSidedAvoidsBlock (backgroundPrepend w b) [3,1,3,1,3] ↔
    (∀ i ∈ List.range w.length, ¬ OneSidedMatchesBlock (backgroundPrepend w b) [3,1,3,1,3] i) ∧
      OneSidedAvoidsBlock b [3,1,3,1,3] := by
  constructor
  · intro h
    exact ⟨fun i _ => h i, fun i hi => h (w.length+i) ((late_match w b _ i).mpr hi)⟩
  · rintro ⟨hi,h⟩ i hm
    by_cases hl : i < w.length
    · exact hi i (List.mem_range.mpr hl) hm
    · have he : w.length+(i-w.length) = i := by omega
      exact h (i-w.length) ((late_match w b _ (i-w.length)).mp (by simpa only [he] using hm))

private theorem safe_prepend (s : BackgroundState) (b : ℕ → ℕ+) :
    Safe s b ↔ OneSidedAvoidsBlock (backgroundPrepend (backgroundStateWord s) b) [3,1,3,1,3] := by
  rw [avoids_prepend]
  cases s <;>
    simp [Safe, Completion, backgroundStateWord, List.range_succ, matches_five,
      backgroundPrepend] <;> tauto

end BackgroundAutomatonSep10
open BackgroundAutomatonSep10

theorem solution (s : BackgroundState) (b : ℕ → ℕ+) :
    BackgroundAllowed s b ↔
      OneSidedAvoidsBlock (backgroundPrepend (backgroundStateWord s) b) [3,1,3,1,3] := by
  exact ⟨fun h => (safe_prepend s b).mp (allowed_safe s b h),
    fun h => safe_allowed s b ((safe_prepend s b).mpr h)⟩

#print axioms solution
