-- Prove2me | solution 1 for DoubleAuctionEff.Repeated.assumption5_le_radius
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:52:18.293019+00:00
-- url     : https://prove2.me/submissions/ec5078e9-79cd-4b61-bfa8-a2ec1ad6d06a

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open DoubleAuctionEff.Repeated

theorem solution {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g : J → ℝ) (r δ : ℝ)
    (hconc : IsConcaveE u) (h5 : Assumption5At u g r δ) :
    ∀ x ∈ Metric.closedBall (0 : J → ℝ) r, ∀ r' : ℝ, 0 < r' → r' ≤ r →
      u x + ((δ * r' : ℝ) : EReal) ≤ u (x + r' • g) := by
  intro x hx r' hr' hrr
  have hr : 0 < r := lt_of_lt_of_le hr' hrr
  -- key: every real level below `u x` transfers to `x + r' g` with gain `δ r'`
  have key : ∀ b : ℝ, (b : EReal) ≤ u x → ((b + δ * r' : ℝ) : EReal) ≤ u (x + r' • g) := by
    intro b hb
    have hA : ((x, b) : (J → ℝ) × ℝ) ∈ {q : (J → ℝ) × ℝ | ((q.2 : ℝ) : EReal) ≤ u q.1} := hb
    have hB : ((x + r • g, b + δ * r) : (J → ℝ) × ℝ) ∈
        {q : (J → ℝ) × ℝ | ((q.2 : ℝ) : EReal) ≤ u q.1} := by
      show ((b + δ * r : ℝ) : EReal) ≤ u (x + r • g)
      rw [EReal.coe_add]
      exact (add_le_add_left hb _).trans (h5 x hx)
    set θ : ℝ := r' / r with hθ
    have hθ0 : 0 ≤ θ := div_nonneg hr'.le hr.le
    have hθ1 : θ ≤ 1 := (div_le_one hr).2 hrr
    have hC := hconc hA hB (sub_nonneg.2 hθ1) hθ0 (by ring)
    have hθr : θ * r = r' := by rw [hθ]; field_simp
    have e1 : (1 - θ) • ((x, b) : (J → ℝ) × ℝ) + θ • (x + r • g, b + δ * r) =
        (x + r' • g, b + δ * r') := by
      ext j
      · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [← hθr]; ring
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [← hθr]; ring
    rw [e1] at hC
    exact hC
  induction h : u x using EReal.rec with
  | bot => simp
  | top =>
    have : u (x + r' • g) = ⊤ := by
      refine EReal.eq_top_iff_forall_lt _ |>.2 fun y => ?_
      have := key (y + 1 - δ * r') (by rw [h]; exact le_top)
      refine lt_of_lt_of_le ?_ this
      rw [EReal.coe_lt_coe_iff]; linarith
    rw [this]; exact le_top
  | coe a =>
    have := key a (le_of_eq h.symm)
    rwa [EReal.coe_add] at this
