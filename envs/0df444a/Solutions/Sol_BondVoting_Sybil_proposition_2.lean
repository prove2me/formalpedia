-- Prove2me | solution 1 for BondVoting.Sybil.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:00:05.15653+00:00
-- url     : https://prove2.me/submissions/a6d5709d-026a-4620-b560-b58485b0c52b

import Mathlib
import Definitions.Def_BondVoting_Sybil_Model

open BondVoting.Sybil

lemma bp_pos (r t : ℝ) : 0 < bondPrice r t := Real.exp_pos _

lemma payoff_lin (r θ u ri q t : ℝ) (ht : 0 < t) :
    bondPayoff r θ u ri q t = q * (|u| * θ / bondPrice r t - (Real.exp (ri * t) - 1)) := by
  have := (bp_pos r t).ne'
  simp only [bondPayoff, bondVote, if_pos ht]
  field_simp

theorem solution (r T : ℝ) (hr : 0 < r) (hT : 0 < T) :
    RobustlyVImplementable (bondVote r) (bondPayoffs r) T := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq t ht
    have hd : HasDerivAt (fun s => q * Real.exp (r * s)) (q * (Real.exp (r * t) * r)) t := by
      have := ((hasDerivAt_id t).const_mul r).exp
      simpa using this.const_mul q
    refine ⟨_, hd.congr_of_eventuallyEq ?_, by have := Real.exp_pos (r * t); positivity⟩
    filter_upwards [lt_mem_nhds ht.1] with s hs
    simp only [bondVote, if_pos hs, bondPrice, Real.exp_neg, div_inv_eq_mul]
  · intro q hq t ht
    refine ⟨fun _ => 1 / bondPrice r t, 0, Filter.Eventually.of_forall fun x => ?_,
      by have := bp_pos r t; positivity, hasDerivAt_const _ _, le_rfl⟩
    have h : (fun y => bondVote r y t) = fun y => y * (1 / bondPrice r t) := by
      funext y; simp only [bondVote, if_pos ht.1]; ring
    rw [h]; simpa using (hasDerivAt_id x).mul_const (1 / bondPrice r t)
  · rintro π ⟨θ, u, ri, _, rfl⟩ q hq M qs ts ⟨⟨hqs0, hsum, hts⟩, hprof⟩
    set g : ℝ → ℝ := fun t => |u| * θ / bondPrice r t - (Real.exp (ri * t) - 1)
    have hpay : attackPayoff (bondPayoff r θ u ri) qs ts = ∑ m, qs m * g (ts m) := by
      unfold attackPayoff
      exact Finset.sum_congr rfl fun m _ => payoff_lin r θ u ri _ _ (hts m).1
    rw [hpay] at hprof
    by_cases hM : ∃ m, 0 ≤ g (ts m)
    · obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image Finset.univ (fun m => g (ts m))
        (by obtain ⟨m, _⟩ := hM; exact ⟨m, Finset.mem_univ _⟩)
      have hg0 : 0 ≤ g (ts m0) := by obtain ⟨m, hm⟩ := hM; exact hm.trans (hmax m (Finset.mem_univ _))
      have h1 := hprof (ts m0) ⟨(hts m0).1.le, (hts m0).2⟩
      rw [payoff_lin r θ u ri _ _ (hts m0).1] at h1
      have h2 : ∑ m, qs m * g (ts m) ≤ ∑ m, qs m * g (ts m0) :=
        Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hmax m (Finset.mem_univ _)) (hqs0 m)
      rw [← Finset.sum_mul] at h2
      have h3 : (∑ m, qs m) * g (ts m0) ≤ q * g (ts m0) := mul_le_mul_of_nonneg_right hsum hg0
      exact absurd h1 (not_lt.mpr (h2.trans h3))
    · push_neg at hM
      have h1 := hprof 0 ⟨le_rfl, hT.le⟩
      have h0 : bondPayoff r θ u ri q 0 = 0 := by simp [bondPayoff]
      rw [h0] at h1
      have : ∑ m, qs m * g (ts m) ≤ 0 :=
        Finset.sum_nonpos fun m _ => mul_nonpos_of_nonneg_of_nonpos (hqs0 m) (hM m).le
      linarith
