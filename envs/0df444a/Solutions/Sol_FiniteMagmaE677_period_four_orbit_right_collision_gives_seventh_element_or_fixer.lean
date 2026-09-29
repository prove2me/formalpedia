-- Prove2me | solution 1 for FiniteMagmaE677.period_four_orbit_right_collision_gives_seventh_element_or_fixer
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-23T20:30:20.561987+00:00
-- url     : https://prove2.me/submissions/b66d129a-8ef8-427e-b45a-26178cbcb83d

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677_seventh_element_growth
import Theorems.Thm_FiniteMagmaE677_period_four_orbit_right_collision_gives_q_packet_or_fixer
import Mathlib.Tactic

/-!
# Proof of period-four seventh-element growth or a fixer
-/

/-!
Standalone solution for the seventh-element D4 growth theorem.  The previously
proved q-packet/fixer theorem supplies the period-four packet; the private
lemmas below prove the branch-preserving seventh source term from that packet.
-/

universe u

private class PMagma (α : Type u) where
  op : α → α → α

local infix:65 " ◇ " => PMagma.op

variable {α : Type u} [PMagma α]

private abbrev PE677 (α : Type u) [PMagma α] : Prop :=
  ∀ x y : α, x = y ◇ (x ◇ ((y ◇ x) ◇ y))

private abbrev PFresh (x c1 c2 c3 q s t : α) : Prop :=
  t ≠ x ∧ t ≠ c1 ∧ t ≠ c2 ∧ t ≠ c3 ∧ t ≠ q ∧ t ≠ s

private theorem p_leftMul_surj (h : PE677 α) (y : α) :
    Function.Surjective (fun x => y ◇ x) := by
  intro x
  exact ⟨x ◇ ((y ◇ x) ◇ y), (h x y).symm⟩

private theorem p_left_cancel [Finite α] (h : PE677 α) (y : α) {a b : α}
    (hab : y ◇ a = y ◇ b) : a = b :=
  ((Finite.surjective_iff_bijective).mp (p_leftMul_surj h y)).1 hab

private theorem q_collision_transport [Finite α] (h : PE677 α)
    {x c1 c2 c3 : α} (hcollision : c2 ◇ x = c3 ◇ x)
    (hpacket2 : c2 ◇ (c2 ◇ x) = c1) :
    (c3 ◇ (c2 ◇ x)) ◇ c3 = c1 ◇ c2 := by
  have hback2 : x = (c2 ◇ x) ◇ ((c2 ◇ (c2 ◇ x)) ◇ c2) := by
    apply p_left_cancel h c2
    exact h (c2 ◇ x) c2
  have hback3 : x = (c3 ◇ x) ◇ ((c3 ◇ (c3 ◇ x)) ◇ c3) := by
    apply p_left_cancel h c3
    exact h (c3 ◇ x) c3
  have hback2' : x = (c2 ◇ x) ◇ (c1 ◇ c2) := by
    simpa only [hpacket2] using hback2
  have hback3' : x = (c2 ◇ x) ◇ ((c3 ◇ (c2 ◇ x)) ◇ c3) := by
    simpa only [← hcollision] using hback3
  exact (p_left_cancel h (c2 ◇ x) (hback2'.symm.trans hback3')).symm

private theorem d4_distinct
    [Finite α] (h : PE677 α) {x c1 c2 c3 : α}
    (hc1 : x ◇ x = c1) (hc2 : x ◇ c1 = c2) (hc3 : x ◇ c2 = c3)
    (hx_ne_c1 : x ≠ c1) (hx_ne_c2 : x ≠ c2) (_hx_ne_c3 : x ≠ c3) :
    c1 ≠ c2 ∧ c1 ≠ c3 ∧ c2 ≠ c3 := by
  have hc1_ne_c2 : c1 ≠ c2 := by
    intro heq
    exact hx_ne_c1 (p_left_cancel h x (hc1.trans (heq.trans hc2.symm)))
  have hc2_ne_c3 : c2 ≠ c3 := by
    intro heq
    exact hc1_ne_c2 (p_left_cancel h x (hc2.trans (heq.trans hc3.symm)))
  have hc1_ne_c3 : c1 ≠ c3 := by
    intro heq
    exact hx_ne_c2 (p_left_cancel h x (hc1.trans (heq.trans hc3.symm)))
  exact ⟨hc1_ne_c2, hc1_ne_c3, hc2_ne_c3⟩

private theorem r_swap_impossible
    (h : PE677 α)
    (hcancel : ∀ a b c : α, a ◇ b = a ◇ c → b = c)
    {x c1 c2 q r : α}
    (hq2 : c2 ◇ x = q)
    (hpacket2 : c2 ◇ q = c1)
    (hr : c1 ◇ c2 = r)
    (hx_ne_r : x ≠ r) :
    ¬ (x ◇ q = r ∧ x ◇ r = q) := by
  rintro ⟨hxq_eq_r, hxr_eq_q⟩
  have hback : ∀ a b : α,
      (a ◇ b) ◇ ((a ◇ (a ◇ b)) ◇ a) = b := by
    intro a b
    apply hcancel a
    exact (h (a ◇ b) a).symm
  have hq_r : q ◇ r = x := by
    apply hcancel c2
    calc
      c2 ◇ (q ◇ r) = q := by simpa only [hpacket2, hr] using (h q c2).symm
      _ = c2 ◇ x := hq2.symm
  have hq_rx : q ◇ (r ◇ x) = r := by
    simpa only [hxr_eq_q, hxq_eq_r] using hback x r
  have hrr_eq_rx : r ◇ r = r ◇ x := by
    simpa only [hq_rx, hq_r, hxq_eq_r] using hback q (r ◇ x)
  have hr_eq_x : r = x := hcancel r r x hrr_eq_rx
  exact hx_ne_r hr_eq_x.symm

private theorem r_two_term_growth
    (h : PE677 α)
    (hcancel : ∀ a b c : α, a ◇ b = a ◇ c → b = c)
    {x c1 c2 c3 q r : α}
    (hc1 : x ◇ x = c1)
    (hc2 : x ◇ c1 = c2)
    (hc3 : x ◇ c2 = c3)
    (hcycle : x ◇ c3 = x)
    (hq2 : c2 ◇ x = q)
    (hpacket1 : c1 ◇ q = x)
    (hpacket2 : c2 ◇ q = c1)
    (hr : c1 ◇ c2 = r)
    (hx_ne_c1 : x ≠ c1)
    (hx_ne_q : x ≠ q)
    (hx_ne_r : x ≠ r)
    (hc1_ne_q : c1 ≠ q)
    (hc1_ne_r : c1 ≠ r)
    (hc2_ne_q : c2 ≠ q)
    (hc2_ne_r : c2 ≠ r)
    (hc3_ne_q : c3 ≠ q)
    (hc3_ne_r : c3 ≠ r)
    (hq_ne_r : q ≠ r) :
    PFresh x c1 c2 c3 q r (x ◇ q) ∨ PFresh x c1 c2 c3 q r (x ◇ r) := by
  have hxc1 : x ◇ (c1 ◇ x) = c3 := by
    apply hcancel x
    calc
      x ◇ (x ◇ (c1 ◇ x)) = x := by simpa only [hc1] using (h x x).symm
      _ = x ◇ c3 := hcycle.symm
  have hc1_x : c1 ◇ x = c2 := by
    apply hcancel x
    exact hxc1.trans hc3.symm
  have hxc2_c1 : x ◇ (c2 ◇ c1) = q := by
    apply hcancel c1
    calc
      c1 ◇ (x ◇ (c2 ◇ c1)) = x := by simpa only [hc1_x] using (h x c1).symm
      _ = c1 ◇ q := hpacket1.symm
  have hc2_c1_ne_q : c2 ◇ c1 ≠ q := by
    intro heq
    have hc1_eq_x : c1 = x := hcancel c2 c1 x (heq.trans hq2.symm)
    exact hx_ne_c1 hc1_eq_x.symm
  have hxq_ne_q : x ◇ q ≠ q := by
    intro heq
    have hq_eq_c2c1 : q = c2 ◇ c1 := hcancel x q (c2 ◇ c1)
      (heq.trans hxc2_c1.symm)
    exact hc2_c1_ne_q hq_eq_c2c1.symm
  by_cases hxq_eq_r : x ◇ q = r
  · right
    constructor
    · intro hxr_eq_x
      exact hc3_ne_r (hcancel x r c3 (hxr_eq_x.trans hcycle.symm)).symm
    constructor
    · intro hxr_eq_c1
      exact hx_ne_r (hcancel x r x (hxr_eq_c1.trans hc1.symm)).symm
    constructor
    · intro hxr_eq_c2
      exact hc1_ne_r (hcancel x r c1 (hxr_eq_c2.trans hc2.symm)).symm
    constructor
    · intro hxr_eq_c3
      exact hc2_ne_r (hcancel x r c2 (hxr_eq_c3.trans hc3.symm)).symm
    constructor
    · intro hxr_eq_q
      exact r_swap_impossible h hcancel hq2 hpacket2 hr hx_ne_r
        ⟨hxq_eq_r, hxr_eq_q⟩
    · intro hxr_eq_r
      have hr_eq_q : r = q := hcancel x r q (hxr_eq_r.trans hxq_eq_r.symm)
      exact hq_ne_r hr_eq_q.symm
  · left
    constructor
    · intro hxq_eq_x
      exact hc3_ne_q (hcancel x q c3 (hxq_eq_x.trans hcycle.symm)).symm
    constructor
    · intro hxq_eq_c1
      exact hx_ne_q (hcancel x q x (hxq_eq_c1.trans hc1.symm)).symm
    constructor
    · intro hxq_eq_c2
      exact hc1_ne_q (hcancel x q c1 (hxq_eq_c2.trans hc2.symm)).symm
    constructor
    · intro hxq_eq_c3
      exact hc2_ne_q (hcancel x q c2 (hxq_eq_c3.trans hc3.symm)).symm
    constructor
    · exact hxq_ne_q
    · exact hxq_eq_r

set_option linter.unusedVariables false in
private theorem s_swap_c2s_fresh
    (h : PE677 α)
    (hcancel : ∀ a b c : α, a ◇ b = a ◇ c → b = c)
    {x c1 c2 c3 q s : α}
    (hc1 : x ◇ x = c1) (hc2 : x ◇ c1 = c2) (hc3 : x ◇ c2 = c3)
    (hcycle : x ◇ c3 = x) (hq2 : c2 ◇ x = q) (hq3 : c3 ◇ x = q)
    (hpacket1 : c1 ◇ q = x) (hpacket2 : c2 ◇ q = c1)
    (hr : c1 ◇ c2 = c1) (hs : c3 ◇ q = s) (htransport : s ◇ c3 = c1)
    (hxq : x ◇ q = s) (hxs : x ◇ s = q)
    (hx_ne_c1 : x ≠ c1) (hx_ne_c2 : x ≠ c2) (hx_ne_c3 : x ≠ c3)
    (hx_ne_q : x ≠ q) (hx_ne_s : x ≠ s)
    (hc1_ne_c2 : c1 ≠ c2) (hc1_ne_c3 : c1 ≠ c3) (hc1_ne_q : c1 ≠ q)
    (hc1_ne_s : c1 ≠ s) (hc2_ne_c3 : c2 ≠ c3) (hc2_ne_q : c2 ≠ q)
    (hc2_ne_s : c2 ≠ s) (hc3_ne_q : c3 ≠ q) (hc3_ne_s : c3 ≠ s)
    (hq_ne_s : q ≠ s) :
    PFresh x c1 c2 c3 q s (c2 ◇ s) := by
  have hback : ∀ a b : α,
      (a ◇ b) ◇ ((a ◇ (a ◇ b)) ◇ a) = b := by
    intro a b
    apply hcancel a
    exact (h (a ◇ b) a).symm
  have hc3_c1 : c3 ◇ c1 = c2 := by
    apply hcancel x
    calc
      x ◇ (c3 ◇ c1) = c3 := by simpa only [hcycle, hc1] using (h c3 x).symm
      _ = x ◇ c2 := hc3.symm
  have hxc1 : x ◇ (c1 ◇ x) = c3 := by
    apply hcancel x
    calc
      x ◇ (x ◇ (c1 ◇ x)) = x := by simpa only [hc1] using (h x x).symm
      _ = x ◇ c3 := hcycle.symm
  have hc1_x : c1 ◇ x = c2 := by
    apply hcancel x
    exact hxc1.trans hc3.symm
  have hxc2_c1 : x ◇ (c2 ◇ c1) = q := by
    apply hcancel c1
    calc
      c1 ◇ (x ◇ (c2 ◇ c1)) = x := by simpa only [hc1_x] using (h x c1).symm
      _ = c1 ◇ q := hpacket1.symm
  have hc2_c1 : c2 ◇ c1 = s := by
    apply hcancel x
    exact hxc2_c1.trans hxs.symm
  have hc1_sc2 : c1 ◇ (s ◇ c2) = q := by
    apply hcancel c2
    calc
      c2 ◇ (c1 ◇ (s ◇ c2)) = c1 := by simpa only [hc2_c1] using (h c1 c2).symm
      _ = c2 ◇ q := hpacket2.symm
  have hq_c2 : q ◇ c2 = s ◇ c2 := by
    simpa only [hc1_sc2, hpacket1, hc2] using hback c1 (s ◇ c2)
  have hs_u_c2 : s ◇ ((c2 ◇ s) ◇ c2) = c1 := by
    simpa only [hc2_c1] using hback c2 c1
  have hu_c2 : (c2 ◇ s) ◇ c2 = c3 := by
    apply hcancel s
    exact hs_u_c2.trans htransport.symm
  constructor
  · intro hu_eq_x
    have hx_sc2 : x ◇ (s ◇ c2) = s := by
      apply hcancel c2
      calc
        c2 ◇ (x ◇ (s ◇ c2)) = x := by
          simpa only [hq2, hq_c2] using (h x c2).symm
        _ = c2 ◇ s := hu_eq_x.symm
    have hsc2_eq_q : s ◇ c2 = q := by
      apply hcancel x
      exact hx_sc2.trans hxq.symm
    have hc1q_eq_q : c1 ◇ q = q := by simpa only [hsc2_eq_q] using hc1_sc2
    exact hx_ne_q (hpacket1.symm.trans hc1q_eq_q)
  constructor
  · intro hu_eq_c1
    have hs_eq_q : s = q := by
      apply hcancel c2
      exact hu_eq_c1.trans hpacket2.symm
    exact hq_ne_s hs_eq_q.symm
  constructor
  · intro hu_eq_c2
    have hc2_c2 : c2 ◇ c2 = c3 := by simpa only [hu_eq_c2] using hu_c2
    have hc2_c3c2 : c2 ◇ (c3 ◇ c2) = s := by
      simpa only [hu_eq_c2, hc2_c2] using hback c2 s
    have hc3_c2 : c3 ◇ c2 = c1 := by
      apply hcancel c2
      exact hc2_c3c2.trans hc2_c1.symm
    have hc2_c1c3 : c2 ◇ (c1 ◇ c3) = c1 := by
      apply hcancel c3
      calc
        c3 ◇ (c2 ◇ (c1 ◇ c3)) = c2 := by
          simpa only [hc3_c2] using (h c2 c3).symm
        _ = c3 ◇ c1 := hc3_c1.symm
    have hc1_c3 : c1 ◇ c3 = q := by
      apply hcancel c2
      exact hc2_c1c3.trans hpacket2.symm
    have hs_c2 : s ◇ c2 = c3 := by
      apply hcancel c1
      exact hc1_sc2.trans hc1_c3.symm
    have hc3_c1s : c3 ◇ (c1 ◇ s) = c2 := by
      apply hcancel s
      calc
        s ◇ (c3 ◇ (c1 ◇ s)) = c3 := by
          simpa only [htransport] using (h c3 s).symm
        _ = s ◇ c2 := hs_c2.symm
    have hc1_eq_c1s : c1 = c1 ◇ s := by
      apply hcancel c3
      exact hc3_c1.trans hc3_c1s.symm
    have hc2_eq_s : c2 = s := by
      apply hcancel c1
      exact hr.trans hc1_eq_c1s
    exact hc2_ne_s hc2_eq_s
  constructor
  · intro hu_eq_c3
    have hc3_c2_eq_c3 : c3 ◇ c2 = c3 := by simpa only [hu_eq_c3] using hu_c2
    have hc2_c3c3 : c2 ◇ (c3 ◇ c3) = c1 := by
      apply hcancel c3
      calc
        c3 ◇ (c2 ◇ (c3 ◇ c3)) = c2 := by
          simpa only [hc3_c2_eq_c3] using (h c2 c3).symm
        _ = c3 ◇ c1 := hc3_c1.symm
    have hc3_c3 : c3 ◇ c3 = q := by
      apply hcancel c2
      exact hc2_c3c3.trans hpacket2.symm
    have hc3_eq_x : c3 = x := by
      apply hcancel c3
      exact hc3_c3.trans hq3.symm
    exact hx_ne_c3 hc3_eq_x.symm
  constructor
  · intro hu_eq_q
    have hs_eq_x : s = x := by
      apply hcancel c2
      exact hu_eq_q.trans hq2.symm
    exact hx_ne_s hs_eq_x.symm
  · intro hu_eq_s
    have hs_eq_c1 : s = c1 := by
      apply hcancel c2
      exact hu_eq_s.trans hc2_c1.symm
    exact hc1_ne_s hs_eq_c1.symm

set_option linter.unusedVariables false in
private theorem s_three_term_growth
    (h : PE677 α)
    (hcancel : ∀ a b c : α, a ◇ b = a ◇ c → b = c)
    {x c1 c2 c3 q s : α}
    (hc1 : x ◇ x = c1) (hc2 : x ◇ c1 = c2) (hc3 : x ◇ c2 = c3)
    (hcycle : x ◇ c3 = x) (hq2 : c2 ◇ x = q) (hq3 : c3 ◇ x = q)
    (hpacket1 : c1 ◇ q = x) (hpacket2 : c2 ◇ q = c1)
    (hr : c1 ◇ c2 = c1) (hs : c3 ◇ q = s) (htransport : s ◇ c3 = c1)
    (hx_ne_c1 : x ≠ c1) (hx_ne_c2 : x ≠ c2) (hx_ne_c3 : x ≠ c3)
    (hx_ne_q : x ≠ q) (hx_ne_s : x ≠ s)
    (hc1_ne_c2 : c1 ≠ c2) (hc1_ne_c3 : c1 ≠ c3) (hc1_ne_q : c1 ≠ q)
    (hc1_ne_s : c1 ≠ s) (hc2_ne_c3 : c2 ≠ c3) (hc2_ne_q : c2 ≠ q)
    (hc2_ne_s : c2 ≠ s) (hc3_ne_q : c3 ≠ q) (hc3_ne_s : c3 ≠ s)
    (hq_ne_s : q ≠ s) :
    PFresh x c1 c2 c3 q s (x ◇ q) ∨
      PFresh x c1 c2 c3 q s (x ◇ s) ∨
      PFresh x c1 c2 c3 q s (c2 ◇ s) := by
  have hq_c1 : q ◇ c1 = x := by
    apply hcancel c2
    calc
      c2 ◇ (q ◇ c1) = q := by simpa only [hpacket2, hr] using (h q c2).symm
      _ = c2 ◇ x := hq2.symm
  have hxq_ne_q : x ◇ q ≠ q := by
    intro hxq_eq_q
    have hqx : q ◇ x = c1 := by
      simpa only [hq_c1, hxq_eq_q, hpacket1] using (h c1 q).symm
    have hq_eq_c1 : q = c1 := by
      simpa only [hxq_eq_q, hqx, hq_c1, hc1] using h q x
    exact hc1_ne_q hq_eq_c1.symm
  by_cases hxq_eq_s : x ◇ q = s
  · by_cases hxs_eq_q : x ◇ s = q
    · exact Or.inr (Or.inr (s_swap_c2s_fresh h hcancel hc1 hc2 hc3 hcycle hq2 hq3
        hpacket1 hpacket2 hr hs htransport hxq_eq_s hxs_eq_q hx_ne_c1 hx_ne_c2
        hx_ne_c3 hx_ne_q hx_ne_s hc1_ne_c2 hc1_ne_c3 hc1_ne_q hc1_ne_s
        hc2_ne_c3 hc2_ne_q hc2_ne_s hc3_ne_q hc3_ne_s hq_ne_s))
    · right
      left
      constructor
      · intro hxs_eq_x
        exact hc3_ne_s ((hcancel x s c3 (hxs_eq_x.trans hcycle.symm)).symm)
      constructor
      · intro hxs_eq_c1
        exact hx_ne_s (hcancel x s x (hxs_eq_c1.trans hc1.symm)).symm
      constructor
      · intro hxs_eq_c2
        exact hc1_ne_s ((hcancel x s c1 (hxs_eq_c2.trans hc2.symm)).symm)
      constructor
      · intro hxs_eq_c3
        exact hc2_ne_s ((hcancel x s c2 (hxs_eq_c3.trans hc3.symm)).symm)
      constructor
      · exact hxs_eq_q
      · intro hxs_eq_s
        exact hq_ne_s ((hcancel x s q (hxs_eq_s.trans hxq_eq_s.symm)).symm)
  · left
    constructor
    · intro hxq_eq_x
      exact hc3_ne_q (hcancel x q c3 (hxq_eq_x.trans hcycle.symm)).symm
    constructor
    · intro hxq_eq_c1
      exact hx_ne_q ((hcancel x q x (hxq_eq_c1.trans hc1.symm)).symm)
    constructor
    · intro hxq_eq_c2
      exact hc1_ne_q ((hcancel x q c1 (hxq_eq_c2.trans hc2.symm)).symm)
    constructor
    · intro hxq_eq_c3
      exact hc2_ne_q ((hcancel x q c2 (hxq_eq_c3.trans hc3.symm)).symm)
    constructor
    · exact hxq_ne_q
    · exact hxq_eq_s

set_option linter.style.haveILetI false in
theorem solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x c1 c2 c3 : α)
    (hc1 : op x x = c1) (hc2 : op x c1 = c2) (hc3 : op x c2 = c3)
    (hcloses : op x c3 = x)
    (hx_ne_c1 : x ≠ c1) (hx_ne_c2 : x ≠ c2) (hx_ne_c3 : x ≠ c3)
    (a b : α)
    (ha : FiniteMagmaE677.InLeftOrbit op x a)
    (hb : FiniteMagmaE677.InLeftOrbit op x b)
    (hab : a ≠ b) (hcollision : op a x = op b x) :
    FiniteMagmaE677.SeventhElementGrowth op x c1 c2 c3 ∨
      FiniteMagmaE677.HasFixerAt op x := by
  letI : PMagma α := ⟨op⟩
  have h' : PE677 α := fun u v => h u v
  rcases FiniteMagmaE677.period_four_orbit_right_collision_gives_q_packet_or_fixer
      op h x c1 c2 c3 hc1 hc2 hc3 hcloses hx_ne_c1 hx_ne_c2 hx_ne_c3 a b ha hb hab
      hcollision with hp | hfix
  · rcases hp with ⟨hcollision', hpacket1, hpacket2, hq_ne_x, hq_ne_c1,
      hq_ne_c2, hq_ne_c3, hbranch⟩
    rcases d4_distinct h' hc1 hc2 hc3 hx_ne_c1 hx_ne_c2 hx_ne_c3 with
      ⟨hc1_ne_c2, hc1_ne_c3, hc2_ne_c3⟩
    rcases hbranch with hr | hs
    · have hr' : c1 ◇ c2 = c1 ◇ c2 := rfl
      have hg := r_two_term_growth h'
        (fun a b c hab => p_left_cancel h' a hab)
        hc1 hc2 hc3 hcloses rfl hpacket1 hpacket2 hr'
        hx_ne_c1 hq_ne_x.symm hr.1.symm hq_ne_c1.symm hr.2.1.symm
        hq_ne_c2.symm hr.2.2.1.symm hq_ne_c3.symm hr.2.2.2.1.symm
        hr.2.2.2.2.symm
      apply Or.inl
      refine ⟨hcollision', hpacket1, hpacket2, hq_ne_x, hq_ne_c1, hq_ne_c2,
        hq_ne_c3, ?_⟩
      left
      refine ⟨hr, ?_⟩
      change PFresh x c1 c2 c3 (c2 ◇ x) (c1 ◇ c2) (x ◇ (c2 ◇ x)) ∨
        PFresh x c1 c2 c3 (c2 ◇ x) (c1 ◇ c2) (x ◇ (c1 ◇ c2))
      exact hg
    · have htransport : (c3 ◇ (c2 ◇ x)) ◇ c3 = c1 := by
        exact (q_collision_transport h' hcollision' hpacket2).trans hs.1
      have hg := s_three_term_growth h'
        (fun a b c hab => p_left_cancel h' a hab)
        hc1 hc2 hc3 hcloses rfl hcollision'.symm hpacket1 hpacket2
        hs.1 rfl htransport hx_ne_c1 hx_ne_c2 hx_ne_c3
        hq_ne_x.symm hs.2.1.symm hc1_ne_c2 hc1_ne_c3 hq_ne_c1.symm
        hs.2.2.1.symm hc2_ne_c3 hq_ne_c2.symm hs.2.2.2.1.symm
        hq_ne_c3.symm hs.2.2.2.2.1.symm hs.2.2.2.2.2.symm
      apply Or.inl
      refine ⟨hcollision', hpacket1, hpacket2, hq_ne_x, hq_ne_c1, hq_ne_c2,
        hq_ne_c3, ?_⟩
      right
      refine ⟨hs, ?_⟩
      change PFresh x c1 c2 c3 (c2 ◇ x) (c3 ◇ (c2 ◇ x)) (x ◇ (c2 ◇ x)) ∨
        PFresh x c1 c2 c3 (c2 ◇ x) (c3 ◇ (c2 ◇ x)) (x ◇ (c3 ◇ (c2 ◇ x))) ∨
        PFresh x c1 c2 c3 (c2 ◇ x) (c3 ◇ (c2 ◇ x))
          (c2 ◇ (c3 ◇ (c2 ◇ x)))
      exact hg
  · exact Or.inr hfix
