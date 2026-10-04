-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsB.potential_criterion_msfp3_integer
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:52:27.395659+00:00
-- url     : https://prove2.me/submissions/c0e8376f-e069-4217-9926-e3c62e59fca3

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsB_DiscreteConvexArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexSet
import Definitions.Def_DiscreteConvex_NetworkFlowsB_M2ConvexSet
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegerValuedArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotentialZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryOptSetMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetZ

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.NetworkFlowsB

namespace PotCex

def tl : Unit → Bool := fun _ => true
def hd : Unit → Bool := fun _ => false

/-- Arc cost `0` on `{0, 3}`, `+∞` elsewhere (midpoint convex, with holes). -/
noncomputable def psi (t : ℤ) : WithTop ℝ := if t = 0 ∨ t = 3 then ((0 : ℝ) : WithTop ℝ) else ⊤

noncomputable def fa : Unit → ℤ → WithTop ℝ := fun _ => psi

abbrev inDom (x : Bool → ℤ) : Prop := x true + x false = 0 ∧ 0 ≤ x true ∧ x true ≤ 3

/-- `f(k,-k) = (k-1)(k-2)` for `0 ≤ k ≤ 3`, `+∞` elsewhere: an M-convex function. -/
noncomputable def f (x : Bool → ℤ) : WithTop ℝ :=
  if inDom x then ((((x true : ℝ) - 1) * ((x true : ℝ) - 2) : ℝ) : WithTop ℝ) else ⊤

theorem f_in {x : Bool → ℤ} (h : inDom x) :
    f x = ((((x true : ℝ) - 1) * ((x true : ℝ) - 2) : ℝ) : WithTop ℝ) := by
  simp only [f]; rw [if_pos h]

theorem dom_of {x : Bool → ℤ} (h : f x ≠ ⊤) : inDom x := by
  by_contra h'; apply h; simp only [f]; rw [if_neg h']

theorem f_exc : MExchangeAxiom f := by
  intro x hx y hy u hu
  have h1 := dom_of hx
  have h2 := dom_of hy
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  refine ⟨!u, ?_, ?_⟩
  · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
    cases u <;> simp at hu ⊢ <;> omega
  · cases u
    · -- u = false: `x true < y true`
      have d1 : inDom (fun w => x w - (if w = false then (1:ℤ) else 0) +
          (if w = (!false) then (1:ℤ) else 0)) := by
        refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
      have d2 : inDom (fun w => y w + (if w = false then (1:ℤ) else 0) -
          (if w = (!false) then (1:ℤ) else 0)) := by
        refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
      rw [f_in ⟨a1, a2, a3⟩, f_in ⟨b1, b2, b3⟩, f_in d1, f_in d2]
      simp only [Bool.not_false, if_true, Bool.true_eq_false, if_false]
      have : x true < y true := by omega
      have hr : (x true : ℝ) + 1 ≤ y true := by exact_mod_cast this
      rw [ge_iff_le, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      push_cast
      nlinarith
    · -- u = true: `y true < x true`
      have d1 : inDom (fun w => x w - (if w = true then (1:ℤ) else 0) +
          (if w = (!true) then (1:ℤ) else 0)) := by
        refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
      have d2 : inDom (fun w => y w + (if w = true then (1:ℤ) else 0) -
          (if w = (!true) then (1:ℤ) else 0)) := by
        refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
      rw [f_in ⟨a1, a2, a3⟩, f_in ⟨b1, b2, b3⟩, f_in d1, f_in d2]
      simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false]
      have hr : (y true : ℝ) + 1 ≤ x true := by exact_mod_cast hu
      rw [ge_iff_le, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      push_cast
      nlinarith

theorem fa_dcu : ∀ a, DiscreteConvexArcZ (fa a) := by
  intro a
  refine ⟨⟨0, by simp [fa, psi]⟩, fun x => ?_⟩
  simp only [fa]
  by_cases h1 : x = 0 ∨ x = 3
  · by_cases h2 : x + 2 = 0 ∨ x + 2 = 3
    · exfalso; omega
    · have : psi (x + 2) = ⊤ := by simp only [psi]; rw [if_neg h2]
      rw [this]; simp
  · have : psi x = ⊤ := by simp only [psi]; rw [if_neg h1]
    rw [this]; simp

theorem bdy (xi : Unit → ℤ) : BoundaryZ tl hd xi = fun b => if b then xi () else -xi () := by
  funext b
  cases b <;> simp [BoundaryZ, tl, hd]

def xi0 : Unit → ℤ := fun _ => 0

theorem gamma_val (xi : Unit → ℤ) (hfe : FeasibleFlowMSFP3Z tl hd fa f xi) :
    Gamma3Z tl hd fa f xi = ((2 : ℝ) : WithTop ℝ) := by
  obtain ⟨h1, h2⟩ := hfe
  have hp := h1 ()
  simp only [fa, psi] at hp
  have ht : xi () = 0 ∨ xi () = 3 := by by_contra h; exact hp (if_neg h)
  have hd' := dom_of h2
  unfold Gamma3Z
  rw [f_in hd', bdy]
  simp only [Finset.univ_unique, Finset.sum_singleton, fa, psi, if_pos ht, if_true]
  rcases ht with ht | ht <;> rw [ht] <;> norm_num

theorem xi0_feas : FeasibleFlowMSFP3Z tl hd fa f xi0 := by
  refine ⟨fun _ => by simp [fa, psi, xi0], ?_⟩
  rw [bdy, f_in (by refine ⟨?_, ?_, ?_⟩ <;> simp [xi0])]
  exact WithTop.coe_ne_top

theorem xi0_opt : OptimalFlowMSFP3Z tl hd fa f xi0 :=
  ⟨xi0_feas, fun xi' h' => by rw [gamma_val _ xi0_feas, gamma_val _ h']⟩

theorem no_pot (p : Bool → ℝ) : ¬ IsOptimalPotentialZ tl hd fa f xi0 p := by
  rintro ⟨h1, h2⟩
  -- arc condition: `0 ≤ 3 (p true - p false)`
  have ha := h1 () 3
  simp only [ReducedArcCostZ, Coboundary, fa, psi, xi0, tl, hd] at ha
  rw [if_pos (by norm_num), if_pos (by norm_num), ← WithTop.coe_add, ← WithTop.coe_add,
    WithTop.coe_le_coe] at ha
  push_cast at ha
  -- boundary condition: compare with `(1,-1)`
  have hb := h2 (fun b => if b then 1 else -1)
  rw [bdy] at hb
  simp only [ReducedBoundaryCostZ, xi0] at hb
  rw [f_in (by refine ⟨?_, ?_, ?_⟩ <;> simp), f_in (by refine ⟨?_, ?_, ?_⟩ <;> simp)] at hb
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false] at hb
  have sub_coe : ∀ r s : ℝ, ((r : ℝ) : WithTop ℝ) - ((s : ℝ) : WithTop ℝ) = ((r - s : ℝ) : WithTop ℝ) := by
    intro r s; norm_cast
  rw [sub_coe, sub_coe, WithTop.coe_le_coe] at hb
  push_cast at hb ha
  linarith

end PotCex

theorem solution : ¬ (∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (tail head : A → V) (fa : A → ℤ → WithTop ℝ)
    (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hfa : ∀ a, DiscreteConvexArcZ (fa a)),
    (∀ xi, FeasibleFlowMSFP3Z tail head fa f xi →
      (OptimalFlowMSFP3Z tail head fa f xi ↔
        ∃ p : V → ℝ, IsOptimalPotentialZ tail head fa f xi p)) ∧
    (∀ xi p, OptimalFlowMSFP3Z tail head fa f xi → IsOptimalPotentialZ tail head fa f xi p →
      ∀ xi', FeasibleFlowMSFP3Z tail head fa f xi' →
        (OptimalFlowMSFP3Z tail head fa f xi' ↔ IsOptimalPotentialZ tail head fa f xi' p)) ∧
    M2ConvexSet (BoundaryOptSetMSFP3Z tail head fa f) ∧
    (((∀ a, IsIntegerValuedArcZ (fa a)) ∧ IsIntegerValuedFn f ∧
        (∃ xi, OptimalFlowMSFP3Z tail head fa f xi)) →
      (∃ pZ : V → ℤ, ∃ xi, OptimalFlowMSFP3Z tail head fa f xi ∧
        IsOptimalPotentialZ tail head fa f xi (fun v => (pZ v : ℝ))) ∧
      LConvexSet (OptimalPotentialSetZ tail head fa f))) := by
  intro h
  obtain ⟨p, hp⟩ := ((h PotCex.tl PotCex.hd PotCex.fa PotCex.f PotCex.f_exc PotCex.fa_dcu).1
    PotCex.xi0 PotCex.xi0_feas).mp PotCex.xi0_opt
  exact PotCex.no_pot p hp

#print axioms solution
