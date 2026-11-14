-- Prove2me | solution 1 for CountingLLL.ContractedWalk.upward_count_segment
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:57:24.74441+00:00
-- url     : https://prove2.me/submissions/cec94093-8b65-4205-89c4-79dcc9212d1b

import Definitions.Def_CountingLLL_ContractedGF

set_option autoImplicit false
open CountingLLL.ContractedWalk
open scoped BigOperators

private def shiftBy (ω : Tape) (n : ℕ) : Tape := fun k => ω (k+n)

private theorem translate_before_hit (ω : Tape) (m : ℕ)
    (h : ∃ t, level ω 1 t = 0) : ∀ t ≤ Nat.find h,
    level ω (m+1) t = m + level ω 1 t := by
  intro t
  induction t with
  | zero => intro ht; simp [level]
  | succ t ih =>
    intro ht
    have ht' : t < Nat.find h := by omega
    have hpos : level ω 1 t ≠ 0 := Nat.find_min h ht'
    have hh := ih (by omega)
    have hpos2 : level ω (m+1) t ≠ 0 := by omega
    simp only [level, hpos, hpos2, if_false]
    rw [hh]
    cases hb : ω t <;> simp [hb] <;> omega

private theorem shift_after_hit (ω : Tape) (m : ℕ) (h : ∃ t, level ω 1 t = 0) (t : ℕ) :
    level ω (m+1) (Nat.find h+t) = level (shiftBy ω (Nat.find h)) m t := by
  induction t with
  | zero =>
    simp only [Nat.add_zero, level]
    rw [translate_before_hit ω m h _ (le_refl _), Nat.find_spec h]
    simp
  | succ t ih =>
    change (if level ω (m+1) (Nat.find h+t) = 0 then 0 else if ω (Nat.find h+t) then level ω (m+1) (Nat.find h+t)+2 else level ω (m+1) (Nat.find h+t)-1) =
      (if level (shiftBy ω (Nat.find h)) m t = 0 then 0 else if (shiftBy ω (Nat.find h)) t then level (shiftBy ω (Nat.find h)) m t+2 else level (shiftBy ω (Nat.find h)) m t-1)
    rw [ih]
    simp [shiftBy, Nat.add_comm]

private theorem split_stop (ω : Tape) (m : ℕ) (h : ∃ t, level ω 1 t = 0)
    (hrest : ∃ t, level (shiftBy ω (Nat.find h)) m t = 0) :
    stopTime ω (m+1) = Nat.find h + Nat.find hrest := by
  classical
  let t := Nat.find h + Nat.find hrest
  have ht : level ω (m+1) t = 0 := by
    dsimp [t]
    rw [shift_after_hit ω m h, Nat.find_spec hrest]
  have hex : ∃ t, level ω (m+1) t = 0 := ⟨t,ht⟩
  have hfind : Nat.find hex = t := by
    apply (Nat.find_eq_iff hex).2
    refine ⟨ht, ?_⟩
    intro j hj
    by_cases hbefore : j < Nat.find h
    · rw [translate_before_hit ω m h j (by omega)]
      have hn := Nat.find_min h hbefore
      omega
    · have hle : Nat.find h ≤ j := by omega
      have hrange : j - Nat.find h < Nat.find hrest := by dsimp [t] at hj; omega
      have heq : j = Nat.find h + (j - Nat.find h) := by omega
      rw [heq, shift_after_hit ω m h]
      exact Nat.find_min hrest hrange
  simp [stopTime, hex, hrest, hfind, t]

private theorem count_split (ω : Tape) (m : ℕ) (h : ∃ t, level ω 1 t = 0)
    (hrest : ∃ t, level (shiftBy ω (Nat.find h)) m t = 0) :
    upwardCount ω (m+1) = upwardCount ω 1 + upwardCount (shiftBy ω (Nat.find h)) m := by
  classical
  unfold upwardCount
  rw [split_stop ω m h hrest]
  simp only [stopTime, dif_pos h]
  rw [Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range (Nat.find h), if level ω (m+1) k ≠ 0 ∧ ω k = true then 1 else 0) =
      (∑ k ∈ Finset.range (Nat.find h), if level ω 1 k ≠ 0 ∧ ω k = true then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hn := Nat.find_min h hk'
    rw [translate_before_hit ω m h k (by omega)]
    have hp : m + level ω 1 k ≠ 0 := by omega
    simp [hn,hp]
  have hsecond : (∑ k ∈ Finset.range (Nat.find hrest), if level ω (m+1) (Nat.find h+k) ≠ 0 ∧ ω (Nat.find h+k) = true then 1 else 0) =
      (∑ k ∈ Finset.range (Nat.find hrest), if level (shiftBy ω (Nat.find h)) m k ≠ 0 ∧ (shiftBy ω (Nat.find h)) k = true then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [shift_after_hit ω m h k]
    simp only [shiftBy, Nat.add_comm]
    rfl
  rw [hfirst,hsecond]
  simp [stopTime, hrest]


theorem solution (ω : Tape) (m : ℕ) (h : ∃ t, level ω 1 t = 0) (hrest : ∃ t, level (fun k => ω (k+stopTime ω 1)) m t = 0) : upwardCount ω (m+1) = upwardCount ω 1 + upwardCount (fun k => ω (k+stopTime ω 1)) m := by
  have hstop : stopTime ω 1 = Nat.find h := by
    unfold stopTime
    rw [dif_pos h]
  rw [hstop] at hrest ⊢
  exact count_split ω m h hrest
