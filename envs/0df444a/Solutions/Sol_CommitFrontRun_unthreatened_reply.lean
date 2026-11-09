-- Prove2me | solution 1 for CommitFrontRun.unthreatened_reply
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:45:26.968285+00:00
-- url     : https://prove2.me/submissions/3b680d4e-ddfd-4605-ba26-0e2eecaa02b0

import Mathlib
import Definitions.Def_CommitFrontRun_Model_IsEquilibrium
import Definitions.Def_CommitFrontRun_Model_sends

open CommitFrontRun in
theorem solution {S Msg : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] (M : Model S Msg)
    (A : StratA S) (B : StratB Msg) (hE : M.IsEquilibrium A B) (s : S) (hp : 0 < M.p s)
    (hthreat : B.threat (M.σA s) = 0) :
    (M.sends s → A.commit s = 1 ∧ A.reveal s = 1) ∧ (¬ M.sends s → A.commit s = 0) := by
  have dev : ∀ x' y' : ℝ, x' ∈ Set.Icc (0:ℝ) 1 → y' ∈ Set.Icc (0:ℝ) 1 →
      M.stateValueA B s x' y' ≤ M.stateValueA B s (A.commit s) (A.reveal s) := by
    intro x' y' hx' hy'
    let A' : StratA S :=
      { commit := Function.update A.commit s x'
        reveal := Function.update A.reveal s y'
        commit_mem := fun t => by
          by_cases h : t = s
          · subst h; rw [Function.update_self]; exact hx'
          · rw [Function.update_of_ne h]; exact A.commit_mem t
        reveal_mem := fun t => by
          by_cases h : t = s
          · subst h; rw [Function.update_self]; exact hy'
          · rw [Function.update_of_ne h]; exact A.reveal_mem t }
    have h := hE.1 A'
    unfold Model.payoffA at h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at h
    have hrest : ∑ t ∈ Finset.univ.erase s, M.p t * M.stateValueA B t (A'.commit t) (A'.reveal t) =
        ∑ t ∈ Finset.univ.erase s, M.p t * M.stateValueA B t (A.commit t) (A.reveal t) := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have hts : t ≠ s := Finset.ne_of_mem_erase ht
      show M.p t * M.stateValueA B t (Function.update A.commit s x' t)
          (Function.update A.reveal s y' t) = _
      rw [Function.update_of_ne hts, Function.update_of_ne hts]
    rw [hrest] at h
    have h2 : M.p s * M.stateValueA B s x' y' ≤
        M.p s * M.stateValueA B s (A.commit s) (A.reveal s) := by
      have e : M.stateValueA B s (A'.commit s) (A'.reveal s) = M.stateValueA B s x' y' := by
        show M.stateValueA B s (Function.update A.commit s x' s)
          (Function.update A.reveal s y' s) = _
        rw [Function.update_self, Function.update_self]
      rw [e] at h
      linarith
    exact le_of_mul_le_mul_left h2 hp
  have hV : ∀ x y, M.stateValueA B s x y = x * (-M.c + M.β * (y * (M.PA s - M.c))) := by
    intro x y
    unfold Model.stateValueA
    rw [hthreat]
    ring
  have hx := A.commit_mem s
  have hy := A.reveal_mem s
  have hc := M.c_pos
  have hβ0 := M.β_nonneg
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · unfold Model.sends at hs
    have hint : M.c < M.β * (M.PA s - M.c) := by
      rcases M.interval s with h | h
      · exact absurd h (not_lt.mpr hs)
      · exact h
    have h11 := dev 1 1 ⟨zero_le_one, le_rfl⟩ ⟨zero_le_one, le_rfl⟩
    rw [hV, hV] at h11
    set x := A.commit s
    set y := A.reveal s
    set w := M.β * (M.PA s - M.c) with hw
    have hw0 : 0 < w := by linarith
    have e1 : M.β * (y * (M.PA s - M.c)) = y * w := by rw [hw]; ring
    have e2 : M.β * (1 * (M.PA s - M.c)) = w := by rw [hw]; ring
    rw [e1, e2, one_mul] at h11
    have hb : -M.c + y * w ≤ -M.c + w := by nlinarith [hy.2]
    have hbpos : 0 < -M.c + y * w := by
      by_contra hneg
      push_neg at hneg
      nlinarith [hx.1]
    have hxb : x * (-M.c + y * w) ≤ -M.c + y * w := by nlinarith [hx.2]
    have hx1 : x = 1 := by
      by_contra hne
      have : x < 1 := lt_of_le_of_ne hx.2 hne
      nlinarith
    have hy1 : y = 1 := by
      by_contra hne
      have : y < 1 := lt_of_le_of_ne hy.2 hne
      nlinarith
    exact ⟨hx1, hy1⟩
  · unfold Model.sends at hs
    push_neg at hs
    have h0 := dev 0 0 ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩
    rw [hV, hV, zero_mul] at h0
    have hneg : M.β * (A.reveal s * (M.PA s - M.c)) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos hβ0
      exact mul_nonpos_of_nonneg_of_nonpos hy.1 (by linarith)
    by_contra hne
    have : 0 < A.commit s := lt_of_le_of_ne hx.1 (Ne.symm hne)
    nlinarith
