-- Prove2me | solution 1 for DoubleAuctionEff.Repeated.remark_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:51:45.905642+00:00
-- url     : https://prove2.me/submissions/73838e3c-d93d-4e27-a9bd-ff5161a44b94

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model

open Matrix DoubleAuctionEff.Repeated

namespace DAERemark6Aux

theorem u_ne_top {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (x : J → ℝ) : u x ≠ ⊤ := by
  intro h
  have hx : x ∈ dom u := by simp [dom, h]
  have := h1.2.2 x hx 1 one_pos
  rw [h] at this
  exact not_top_lt this

theorem mono_g {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (z : J → ℝ) {s : ℝ} (hs : 0 ≤ s) : u z ≤ u (z + s • g) := by
  rcases hs.lt_or_eq with hs | hs
  · by_cases hz : z ∈ dom u
    · exact (h1.2.2 z hz s hs).le
    · simp only [dom, Set.mem_setOf_eq, not_lt, le_bot_iff] at hz
      simp [hz]
  · subst hs; simp

theorem le_indiff {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {r : ℝ}
    (h : u x0 ≤ u (x0 + y - r • g)) : (r : EReal) ≤ indiffPrice u g x0 y := by
  unfold indiffPrice
  exact le_iSup₂ (f := fun (r : ℝ) (_ : u x0 ≤ u (x0 + y - r • g)) => (r : EReal)) r h

theorem indiff_zero_nonneg {J : Type*} (u : (J → ℝ) → EReal) (g x0 : J → ℝ) :
    (0 : EReal) ≤ indiffPrice u g x0 0 := by
  have := le_indiff (u := u) (g := g) (x0 := x0) (y := 0) (r := 0) (by simp)
  simpa using this

/-- If the indifference price is finite, the agent's endowment is in the domain. -/
theorem mem_dom_of_finite {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {c : ℝ}
    (hc : indiffPrice u g x0 y = (c : EReal)) : x0 ∈ dom u := by
  by_contra hx
  simp only [dom, Set.mem_setOf_eq, not_lt, le_bot_iff] at hx
  have := le_indiff (u := u) (g := g) (x0 := x0) (y := y) (r := c + 1) (by simp [hx])
  rw [hc, EReal.coe_le_coe_iff] at this
  linarith

/-- The supremum defining a finite indifference price is attained (upper semicontinuity). -/
theorem indiff_attained {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {c : ℝ}
    (husc : UpperSemicontinuous u) (hc : indiffPrice u g x0 y = (c : EReal)) :
    u x0 ≤ u (x0 + y - c • g) := by
  by_contra hlt
  push_neg at hlt
  have hcont : Continuous (fun r : ℝ => x0 + y - r • g) := by fun_prop
  have hev : ∀ᶠ r in nhds c, u (x0 + y - r • g) < u x0 :=
    hcont.continuousAt.eventually (husc _ _ hlt)
  rcases Metric.eventually_nhds_iff.1 hev with ⟨ε, hε, hball⟩
  have hle : indiffPrice u g x0 y ≤ ((c - ε : ℝ) : EReal) := by
    unfold indiffPrice
    refine iSup₂_le fun r hr => ?_
    have hrc : (r : EReal) ≤ c := hc ▸ le_indiff hr
    rw [EReal.coe_le_coe_iff] at hrc ⊢
    by_contra hcon
    push_neg at hcon
    have hd : dist r c < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    exact absurd hr (not_le.2 (hball hd))
  rw [hc, EReal.coe_le_coe_iff] at hle
  linarith

end DAERemark6Aux

open DAERemark6Aux in
theorem solution {J : Type*} [Fintype J] (u : (J → ℝ) → EReal) (g x0 xbar p : J → ℝ)
    (h1 : Assumption1 u g) (hp : IsSupergrad (indiffPrice u g x0) xbar p) (c : ℝ)
    (hc : indiffPrice u g x0 xbar = (c : EReal)) :
    0 ≤ c - p ⬝ᵥ xbar ∧ u (x0 + xbar - c • g) ≤ u (x0 + xbar - (p ⬝ᵥ xbar) • g) ∧
      u x0 ≤ u (x0 + xbar - c • g) ∧ u x0 ≤ u (x0 + xbar - (p ⬝ᵥ xbar) • g) ∧
      (c ≠ p ⬝ᵥ xbar → u x0 < u (x0 + xbar - (p ⬝ᵥ xbar) • g)) := by
  -- the surplus is nonnegative
  have hs : 0 ≤ c - p ⬝ᵥ xbar := by
    have h0 := hp.2 0
    rw [hc] at h0
    have h00 := (indiff_zero_nonneg u g x0).trans h0
    rw [← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff] at h00
    simp only [zero_sub, dotProduct_neg] at h00
    linarith
  have heq : x0 + xbar - (p ⬝ᵥ xbar) • g = (x0 + xbar - c • g) + (c - p ⬝ᵥ xbar) • g := by
    rw [sub_smul]; abel
  have hmono : u (x0 + xbar - c • g) ≤ u (x0 + xbar - (p ⬝ᵥ xbar) • g) := by
    rw [heq]; exact mono_g h1 _ hs
  have hatt : u x0 ≤ u (x0 + xbar - c • g) := indiff_attained h1.1 hc
  refine ⟨hs, hmono, hatt, hatt.trans hmono, fun hne => ?_⟩
  have hspos : 0 < c - p ⬝ᵥ xbar := lt_of_le_of_ne hs (fun h => hne (by linarith))
  have hx0 : x0 ∈ dom u := mem_dom_of_finite hc
  have hz : x0 + xbar - c • g ∈ dom u := lt_of_lt_of_le hx0 hatt
  rw [heq]
  exact lt_of_le_of_lt hatt (h1.2.2 _ hz _ hspos)
