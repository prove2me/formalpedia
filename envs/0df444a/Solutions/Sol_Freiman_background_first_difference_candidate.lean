-- Prove2me | solution 1 for Freiman.background_first_difference_candidate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:04:48.849981+00:00
-- url     : https://prove2.me/submissions/4371a549-19c9-4418-b30e-205354c6d4ed

import Definitions.Def_Freiman_backgroundWords
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

open Freiman

namespace BackgroundCandidateSep10
private theorem reference_even (r : Bool) (k : ℕ) (hk : k % 2 = 0) :
    backgroundReference r k = 1 := by
  have hres : k % 6 = 0 ∨ k % 6 = 2 ∨ k % 6 = 4 := by omega
  cases r <;> rcases hres with h | h | h <;>
    norm_num [backgroundReference, backgroundT, backgroundU, gapEventuallyPeriodic, h]
end BackgroundCandidateSep10

theorem solution (r : Bool) (b : ℕ → ℕ+)
    (hb : ∀ n : ℕ, (b n : ℕ) ≤ 4)
    (h14 : OneSidedAvoidsBlock b [1,4])
    (ha : BackgroundAllowed (backgroundReferenceState r) b)
    (n : ℕ) (hp : ∀ k : ℕ, k < n → b k = backgroundReference r k)
    (hs : backgroundRun (backgroundReferenceState r)
      ((List.range n).map (backgroundReference r)) = some (backgroundPhaseState r n)) :
    BackgroundCandidate r n (b n) := by
  have hm : (List.range n).map b = (List.range n).map (backgroundReference r) :=
    List.map_congr_left fun k hk => hp k (List.mem_range.mp hk)
  have hr : backgroundRun (backgroundReferenceState r) ((List.range n).map b) =
      some (backgroundPhaseState r n) := by rw [hm]; exact hs
  have hstep : backgroundStep (backgroundPhaseState r n) (b n) ≠ none := by
    have hn := ha (n+1)
    have heq : backgroundRun (backgroundReferenceState r) ((List.range (n+1)).map b) =
        backgroundStep (backgroundPhaseState r n) (b n) := by
      simp only [List.range_succ, List.map_append, List.map_singleton, backgroundRun,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (backgroundRun (backgroundReferenceState r) ((List.range n).map b)).bind
        (fun s => backgroundStep s (b n)) = _
      rw [hr]
      rfl
    rwa [heq] at hn
  refine ⟨hb n, hstep, ?_⟩
  intro hn hd
  have hnmod : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using hn
  have hprev : n-1 < n := by omega
  have hprevmod : (n-1) % 2 = 0 := by omega
  have hprevval : b (n-1) = 1 := (hp (n-1) hprev).trans
    (BackgroundCandidateSep10.reference_even r (n-1) hprevmod)
  apply h14 (n-1)
  intro k hk
  have hk' : k < 2 := hk
  have hkn : k = 0 ∨ k = 1 := by omega
  have hsum : n-1+1 = n := by omega
  rcases hkn with rfl | rfl
  · simp [hprevval, List.getD]
  · simp [hsum, hd, List.getD]

#print axioms solution
