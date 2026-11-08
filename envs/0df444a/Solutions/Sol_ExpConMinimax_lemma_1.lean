-- Prove2me | solution 1 for ExpConMinimax.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:54:20.654193+00:00
-- url     : https://prove2.me/submissions/4bdaef34-833f-4e29-beb0-6341f5844b81

import Mathlib
import Definitions.Def_ExpConMinimax_IsSaddlePoint

namespace Aux_ExpConMinimax_l1
open ExpConMinimax

theorem inner_le_pos {m : ℕ} (γ v : Vec m) (hγ : IsNonneg γ) :
    inner ℝ γ v ≤ ‖γ‖ * ‖vecPosPart v‖ := by
  have h1 : inner ℝ γ v ≤ inner ℝ γ (vecPosPart v) := by
    simp only [PiLp.inner_apply, vecPosPart, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [le_max_left (v i) 0, hγ i]
  exact h1.trans (real_inner_le_norm _ _)

end Aux_ExpConMinimax_l1

open ExpConMinimax Aux_ExpConMinimax_l1 in
theorem solution {dx dy m₁ m₂ : ℕ} (P : Problem dx dy m₁ m₂) (hP : P.Standing)
    (xs : Vec dx) (ys : Vec dy) (γs : Vec m₁) (lams : Vec m₂)
    (hsad : IsSaddlePoint P xs ys γs lams) :
    ∀ x ∈ P.X, ∀ y ∈ P.Y,
      -(‖γs‖ * ‖vecPosPart (P.H x)‖) - ‖lams‖ * ‖vecPosPart (P.G y)‖ ≤ P.F x ys - P.F xs y ∧
      -(max ‖γs‖ ‖lams‖ * (‖vecPosPart (P.H x)‖ + ‖vecPosPart (P.G y)‖)) ≤
        -(‖γs‖ * ‖vecPosPart (P.H x)‖) - ‖lams‖ * ‖vecPosPart (P.G y)‖ := by
  obtain ⟨hxs, hys, hγs, hls, hS⟩ := hsad
  have h0m1 : IsNonneg (0 : Vec m₁) := fun i => by simp
  have h0m2 : IsNonneg (0 : Vec m₂) := fun i => by simp
  intro x hx y hy
  constructor
  · have h1 := (hS x hx ys hys γs hγs lams hls).1
    have h2 := (hS xs hxs y hy γs hγs lams hls).2
    have h3 := (hS xs hxs ys hys γs hγs 0 h0m2).1
    have h4 := (hS xs hxs ys hys 0 h0m1 lams hls).2
    simp only [Problem.lagrangian, inner_zero_left] at h1 h2 h3 h4
    have i1 := inner_le_pos γs (P.H x) hγs
    have i2 := inner_le_pos lams (P.G y) hls
    linarith
  · have a1 := norm_nonneg (vecPosPart (P.H x))
    have a2 := norm_nonneg (vecPosPart (P.G y))
    have m1 := le_max_left ‖γs‖ ‖lams‖
    have m2 := le_max_right ‖γs‖ ‖lams‖
    nlinarith
