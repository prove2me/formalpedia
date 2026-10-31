-- Prove2me | solution 1 for DoubleAuctionEff.Repeated.auction_gain
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:55:49.81849+00:00
-- url     : https://prove2.me/submissions/d659ad1d-3953-4f86-9d42-fc05e0d30e83

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model
import Theorems.Thm_DoubleAuctionEff_Repeated_remark_6
import Theorems.Thm_DoubleAuctionEff_Repeated_assumption5_le_radius

open Matrix DoubleAuctionEff.Repeated

theorem solution {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g x0 xbar p : J → ℝ)
    (h1 : Assumption1 u g) (hp : IsSupergrad (indiffPrice u g x0) xbar p) (c : ℝ)
    (hc : indiffPrice u g x0 xbar = (c : EReal)) (r δ : ℝ) (hr : 0 < r)
    (h5 : Assumption5At u g r δ)
    (hball : x0 + xbar - c • g ∈ Metric.closedBall (0 : J → ℝ) r)
    (hsurplus : c - p ⬝ᵥ xbar ≤ r) :
    u x0 + ((δ * (c - p ⬝ᵥ xbar) : ℝ) : EReal) ≤ u (x0 + xbar - (p ⬝ᵥ xbar) • g) := by
  obtain ⟨hs, -, hatt, hle, -⟩ := remark_6 u g x0 xbar p h1 hp c hc
  have heq : x0 + xbar - (p ⬝ᵥ xbar) • g = (x0 + xbar - c • g) + (c - p ⬝ᵥ xbar) • g := by
    rw [sub_smul]; abel
  rcases hs.lt_or_eq with hpos | hzero
  · rw [heq]
    exact (add_le_add_left hatt _).trans
      (assumption5_le_radius u g r δ h1.2.1 h5 _ hball _ hpos hsurplus)
  · rw [← hzero]; simpa using hle
