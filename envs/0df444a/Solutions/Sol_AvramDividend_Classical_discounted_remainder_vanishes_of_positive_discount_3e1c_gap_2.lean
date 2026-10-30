-- Prove2me | solution 2 for AvramDividend.Classical.discounted_remainder_vanishes_of_positive_discount_3e1c_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:54:52.847345+00:00
-- url     : https://prove2.me/submissions/30346ad2-cfe4-4b11-b8f9-058824c3fd21

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

-- Proof draft for pending publication:
-- AvramDividend.Classical.discounted_remainder_vanishes_of_positive_discount_3e1c_gap
-- Pure Mathlib; no Prove2Me premises. Staged while publication job
-- 325b7ec0-8f73-4a48-8e49-d78891260e24 is coordinator-owned PENDING.
-- On PUBLISHED, submit via lint-submit with the exact new theorem UUID.
-- Mathematical route: t ↦ q * t tends to +∞ for q > 0; composing with
-- exp(-·) → 0 and multiplying the limit by the constant C (0 * C = 0).
-- Pinned revision: 0df444a360eaa60ab8c11dca51a86af692955474
-- (Real.tendsto_exp_neg_atTop_nhds_zero index-confirmed at this revision;
-- const_mul_atTop / mul_const / tendsto_id applicability left to verifier).
-- No local Lean was run. Remote verifier decides.
theorem solution
    (q C : ℝ) (hq : 0 < q) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(q * t)) * C) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun t : ℝ => q * t) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hq tendsto_id
  have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-(q * t))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h3 := h2.mul_const C
  simpa using h3
