-- Prove2me | solution 1 for FiniteMagmaE677.period_four_orbit_right_collision_gives_fixer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-23T20:58:57.573987+00:00
-- url     : https://prove2.me/submissions/14d08c8f-b0a5-4492-8799-069dc4c57bdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Theorems.Thm_FiniteMagmaE677_period_four_r_first_return_gives_fixer
import Theorems.Thm_FiniteMagmaE677_period_four_fixed_seed_cycle_gives_fixer
import Theorems.Thm_FiniteMagmaE677_period_four_s_first_return_gives_fixer
import Theorems.Thm_FiniteMagmaE677_period_four_s_second_step_return_gives_fixer
import Theorems.Thm_FiniteMagmaE677_period_four_cross_cycle_collision_gives_fixer
import Theorems.Thm_FiniteMagmaE677_period_four_orbit_right_collision_gives_first_return_or_fixer
import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.EquivFin

/-! Source-local algebra for the two refined D4 cycle-contact branches. -/

namespace FiniteMagmaE677

universe u

private theorem contact_left_bijective
    {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op) (y : α) :
    Function.Bijective (op y) := by
  have hs : Function.Surjective (op y) := by
    intro x
    exact ⟨op x (op (op y x) y), (h x y).symm⟩
  exact Finite.surjective_iff_bijective.mp hs

private theorem contact_backward_recurrence
    {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op) (x y : α) :
    x = op (op y x) (op (op y (op y x)) y) := by
  exact (contact_left_bijective op h y).injective (h (op y x) y)

/-- The R-through-two contact supplies a fixer at the outsider seed. -/
theorem d4_contact_seed_fixer
    {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op)
    (x c1 c2 : α)
    (hreturn : op c2 (op c2 x) = c1)
    (hcontact : op x (op c2 x) = op c1 c2) :
    HasFixerAt op (op c2 x) := by
  have hinj := fun a ↦ (contact_left_bijective op h a).injective
  have hqr : op (op c2 x) (op c1 c2) = x := by
    apply hinj c2
    calc
      op c2 (op (op c2 x) (op c1 c2)) = op c2 x := by
        simpa only [hreturn] using (h (op c2 x) c2).symm
      _ = op c2 x := rfl
  have hcross : op (op c2 x) (op x (op c2 x)) = x := by
    rw [hcontact]
    exact hqr
  have hphase : op c2 x = op (op (op c2 x) x) (op c2 x) := by
    apply hinj x
    apply hinj (op c2 x)
    exact hcross.trans (h x (op c2 x))
  exact ⟨op (op c2 x) x, hphase.symm⟩

/-- The swapped-S bridge gives the normalized cross-cycle star identity. -/
theorem d4_contact_swap_star
    {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op)
    (x c1 c2 c3 t : α)
    (hxx : op x x = c1)
    (hxc2 : op x c2 = c3)
    (hxc3 : op x c3 = x)
    (hbridge : op t c2 = c3) :
    op (op t c3) t = c1 := by
  apply (contact_left_bijective op h c3).injective
  calc
    op c3 (op (op t c3) t) = c2 := by
      simpa only [hbridge] using (contact_backward_recurrence op h c2 t).symm
    _ = op c3 c1 := by
      simpa only [hxc2, hxc3, hxx] using contact_backward_recurrence op h c2 x

end FiniteMagmaE677

universe u

open FiniteMagmaE677.FirstReturn

theorem solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x c1 c2 c3 : α)
    (hc1 : op x x = c1)
    (hc2 : op x c1 = c2)
    (hc3 : op x c2 = c3)
    (hcloses : op x c3 = x)
    (hx_ne_c1 : x ≠ c1)
    (hx_ne_c2 : x ≠ c2)
    (hx_ne_c3 : x ≠ c3)
    (a b : α)
    (ha : FiniteMagmaE677.InLeftOrbit op x a)
    (hb : FiniteMagmaE677.InLeftOrbit op x b)
    (hab : a ≠ b)
    (hcollision : op a x = op b x)
    : FiniteMagmaE677.HasFixerAt op x := by
  rcases FiniteMagmaE677.period_four_orbit_right_collision_gives_first_return_or_fixer
      op h x c1 c2 c3 hc1 hc2 hc3 hcloses hx_ne_c1 hx_ne_c2 hx_ne_c3
      a b ha hb hab hcollision with hpacket | hfix
  · obtain ⟨input⟩ := hpacket
    have packet := input.distinguished
    cases input.branch with
    | rSeedQThroughOne start fresh initial_trace first_return =>
        exact FiniteMagmaE677.period_four_r_first_return_gives_fixer
          op h x c1 c2 c3 packet start fresh initial_trace first_return
    | rSeedQThroughTwo start q_to_r fresh initial_trace first_return =>
        have seed_fixer := FiniteMagmaE677.d4_contact_seed_fixer
          op h x c1 c2 packet.q_packet_return q_to_r
        exact FiniteMagmaE677.period_four_fixed_seed_cycle_gives_fixer
          op h x c1 c2 c3 packet start q_to_r fresh initial_trace first_return seed_fixer
    | sSeedQThroughOne start fresh initial_trace first_return =>
        exact FiniteMagmaE677.period_four_s_first_return_gives_fixer
          op h x c1 c2 c3 packet start fresh initial_trace first_return
    | sSeedQThroughTwo start q_to_s fresh initial_trace first_return =>
        exact FiniteMagmaE677.period_four_s_second_step_return_gives_fixer
          op h x c1 c2 c3 packet start q_to_s fresh initial_trace first_return
    | sSwapSeedT start q_to_s s_to_q fresh initial_trace first_return bridge =>
        have star := FiniteMagmaE677.d4_contact_swap_star
          op h x c1 c2 c3 (op c2 (op c3 (op c2 x)))
          packet.orbit_c1 packet.orbit_c3 packet.orbit_closes bridge
        exact FiniteMagmaE677.period_four_cross_cycle_collision_gives_fixer
          op h x c1 c2 c3 packet start q_to_s s_to_q fresh initial_trace first_return bridge star
  · exact hfix
