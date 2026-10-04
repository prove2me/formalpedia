-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsC.gs_characterizes_mconvex
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:17:47.19124+00:00
-- url     : https://prove2.me/submissions/6e4abc1f-1879-49a9-81b4-c9b6ed4828d3

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MGS
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatGS
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureValOn

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.MConvexFunctionsC

namespace Nat1D

/-- The indicator (value `0`) of `{0, 1} ⊆ ℤ`: an M♮-convex function of one variable. -/
noncomputable def f (x : Unit → ℤ) : WithTop ℝ :=
  if 0 ≤ x () ∧ x () ≤ 1 then ((0 : ℝ) : WithTop ℝ) else ⊤

theorem f_in {x : Unit → ℤ} (h : 0 ≤ x () ∧ x () ≤ 1) : f x = ((0 : ℝ) : WithTop ℝ) := by
  simp only [f]; rw [if_pos h]

theorem f_out {x : Unit → ℤ} (h : ¬ (0 ≤ x () ∧ x () ≤ 1)) : f x = ⊤ := by
  simp only [f]; rw [if_neg h]

theorem dom_lift {z : Option Unit → ℤ} (hz : z ∈ DomZ (LiftedFunction f)) :
    z none = -z (some ()) ∧ 0 ≤ z (some ()) ∧ z (some ()) ≤ 1 := by
  by_contra h
  apply hz
  unfold LiftedFunction
  simp only [Finset.univ_unique, Finset.sum_singleton]
  by_cases h1 : z none = -z (some ())
  · rw [if_pos (by simpa using h1)]
    exact f_out (fun h2 => h ⟨h1, h2⟩)
  · rw [if_neg (by simpa using h1)]

theorem lift_val (z : Option Unit → ℤ) (h1 : z none = -z (some ())) (h2 : 0 ≤ z (some ()))
    (h3 : z (some ()) ≤ 1) : LiftedFunction f z = ((0 : ℝ) : WithTop ℝ) := by
  unfold LiftedFunction
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [if_pos (by simpa using h1)]
  exact f_in ⟨h2, h3⟩

theorem f_mnat : MNaturalConvex f := by
  intro x hx y hy u hu
  obtain ⟨hx1, hx2, hx3⟩ := dom_lift hx
  obtain ⟨hy1, hy2, hy3⟩ := dom_lift hy
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  cases u with
  | none =>
    refine ⟨some (), by simp [SuppNeg]; omega, ?_⟩
    rw [lift_val x hx1 hx2 hx3, lift_val y hy1 hy2 hy3,
      lift_val _ (by simp [CharVec]; omega) (by simp [CharVec]; omega) (by simp [CharVec]; omega),
      lift_val _ (by simp [CharVec]; omega) (by simp [CharVec]; omega) (by simp [CharVec]; omega)]
  | some u =>
    have : u = () := Subsingleton.elim _ _
    subst this
    refine ⟨none, by simp [SuppNeg]; omega, ?_⟩
    rw [lift_val x hx1 hx2 hx3, lift_val y hy1 hy2 hy3,
      lift_val _ (by simp [CharVec]; omega) (by simp [CharVec]; omega) (by simp [CharVec]; omega),
      lift_val _ (by simp [CharVec]; omega) (by simp [CharVec]; omega) (by simp [CharVec]; omega)]

/-- `f[w](x) = f(x) - w x` in one variable. -/
theorem lw (w : Unit → ℝ) (x : Unit → ℤ) :
    LinearWeight f w x = f x + ((-(w () * (x () : ℝ)) : ℝ) : WithTop ℝ) := by
  simp [LinearWeight]

end Nat1D

namespace Nat1D

theorem sInf_sub_top {s : Set (WithTop ℝ)} (h : s ⊆ {⊤}) : sInf s = ⊤ := by
  classical
  exact if_pos (Or.inl h)

theorem sInf_zero {s : Set (WithTop ℝ)} (h : s ⊆ {((0 : ℝ) : WithTop ℝ), ⊤})
    (h0 : ((0 : ℝ) : WithTop ℝ) ∈ s) : sInf s = ((0 : ℝ) : WithTop ℝ) := by
  have hpre : ((fun r : ℝ => (r : WithTop ℝ)) ⁻¹' s) = {0} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hr
      rcases h hr with h' | h'
      · exact WithTop.coe_injective h'
      · exact absurd h' WithTop.coe_ne_top
    · rintro rfl; exact h0
  rw [WithTop.sInf_eq (fun hs => WithTop.coe_ne_top (hs h0))
    ⟨((0 : ℝ) : WithTop ℝ), fun y hy => by
      rcases h hy with h' | h'
      · rw [h']
      · rw [h']; exact le_top⟩, hpre, csInf_singleton]

/-- Every value of `ConvexClosureValOn f S p` is `0`, and one exists iff `p` is a convex
combination of points of `S ⊆ dom f`. -/
theorem on_sub (S : Finset (Unit → ℤ)) (p : Unit → ℝ) :
    {L : WithTop ℝ | ∃ lam : (Unit → ℤ) → ℝ,
      (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ f) ∧
      (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = p v) ∧
      L = ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ)} ⊆ {((0 : ℝ) : WithTop ℝ)} := by
  rintro L ⟨lam, -, -, hdom, -, rfl⟩
  simp only [Set.mem_singleton_iff]
  congr 1
  refine Finset.sum_eq_zero (fun y hy => ?_)
  have : 0 ≤ y () ∧ y () ≤ 1 := by
    by_contra h; exact hdom y hy (f_out h)
  rw [f_in this]; simp

theorem f_ce : ConvexExtensible f := by
  intro x
  unfold ConvexClosureVal
  by_cases hx : 0 ≤ x () ∧ x () ≤ 1
  · rw [f_in hx]
    apply sInf_zero
    · rintro L ⟨S, hS, rfl⟩
      unfold ConvexClosureValOn
      by_cases hne : ({L : WithTop ℝ | ∃ lam : (Unit → ℤ) → ℝ,
          (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ f) ∧
          (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = (fun v => ((x v : ℤ) : ℝ)) v) ∧
          L = ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ)}).Nonempty
      · obtain ⟨L0, hL0⟩ := hne
        have h0 := on_sub S _ hL0
        rw [Set.mem_singleton_iff] at h0
        subst h0
        left
        exact sInf_zero (fun y hy => Or.inl (on_sub S _ hy)) hL0
      · right
        rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        exact WithTop.sInf_empty
    · refine ⟨{x}, ?_, ?_⟩
      · intro y hy; rw [Finset.mem_singleton] at hy; subst hy; show f _ ≠ ⊤; rw [f_in hx]
        exact WithTop.coe_ne_top
      unfold ConvexClosureValOn
      symm
      apply sInf_zero (fun y hy => Or.inl (on_sub _ _ hy))
      refine ⟨fun _ => 1, by simp, by simp, ?_, by simp, ?_⟩
      · intro y hy; rw [Finset.mem_singleton] at hy; subst hy; show f _ ≠ ⊤; rw [f_in hx]
        exact WithTop.coe_ne_top
      · simp [f_in hx]
  · rw [f_out hx]
    apply sInf_sub_top
    rintro L ⟨S, hS, rfl⟩
    simp only [Set.mem_singleton_iff]
    unfold ConvexClosureValOn
    apply sInf_sub_top
    rintro L ⟨lam, hlam, hsum, hdom, hcomb, rfl⟩
    exfalso
    apply hx
    have hcoord : ∀ y ∈ S, (0 : ℝ) ≤ y () ∧ (y () : ℝ) ≤ 1 := by
      intro y hy
      have : 0 ≤ y () ∧ y () ≤ 1 := by
        by_contra h; exact hdom y hy (f_out h)
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
    have hc := hcomb ()
    have lo : (0 : ℝ) ≤ ∑ y ∈ S, lam y * (y () : ℝ) :=
      Finset.sum_nonneg (fun y hy => mul_nonneg (hlam y hy) (hcoord y hy).1)
    have hi : ∑ y ∈ S, lam y * (y () : ℝ) ≤ ∑ y ∈ S, lam y :=
      Finset.sum_le_sum (fun y hy => by
        have := mul_le_mul_of_nonneg_left (hcoord y hy).2 (hlam y hy); linarith)
    rw [hc] at lo hi
    rw [hsum] at hi
    have lo' : (0 : ℝ) ≤ (x () : ℝ) := lo
    have hi' : (x () : ℝ) ≤ 1 := hi
    exact ⟨by exact_mod_cast lo', by exact_mod_cast hi'⟩

end Nat1D

namespace Nat1D

theorem not_mnatgs : ¬ MNatGS f := by
  intro H
  have hx : (fun _ => (1 : ℤ)) ∈ ArgMinOn (LinearWeight f (fun v => (fun _ => (0 : ℝ)) v - 0)) := by
    intro y
    rw [lw, lw, f_in (by simp)]
    simp only [sub_zero, zero_mul, neg_zero]
    by_cases hy : 0 ≤ y () ∧ y () ≤ 1
    · rw [f_in hy]
    · rw [f_out hy]; exact le_top
  have hz : (fun _ => (0 : ℤ)) ∈ ArgMinOn (LinearWeight f (fun v => (fun _ => (0 : ℝ)) v - 1)) := by
    intro y
    rw [lw, lw, f_in (by simp)]
    by_cases hy : 0 ≤ y () ∧ y () ≤ 1
    · rw [f_in hy, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      have : (0 : ℝ) ≤ y () := by exact_mod_cast hy.1
      push_cast; linarith
    · rw [f_out hy]; simp
  obtain ⟨y, hy, hge, -⟩ := H (fun _ => 0) (fun _ => 0) 0 1 (fun _ => le_rfl) zero_le_one _ hx
    ⟨_, hz⟩
  have h1 := hge () rfl
  have hle := hy (fun _ => 0)
  rw [lw, lw, f_in (x := fun _ => 0) (by simp)] at hle
  by_cases hyd : 0 ≤ y () ∧ y () ≤ 1
  · rw [f_in hyd, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
    have : (1 : ℝ) ≤ y () := by exact_mod_cast h1
    push_cast at hle; linarith
  · rw [f_out hyd, top_add, ← WithTop.coe_add] at hle
    exact WithTop.coe_ne_top (top_le_iff.mp hle)

end Nat1D

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hce : ConvexExtensible f) (hne : (DomZ f).Nonempty) (hbdd : (DomZ f).Finite),
    ((∃ r : ℤ, ∀ x ∈ DomZ f, ∑ v, x v = r) → (MExchangeAxiom f ↔ MGS f)) ∧
    (MNaturalConvex f ↔ MNatGS f)) := by
  intro h
  have hdom : DomZ Nat1D.f ⊆ {fun _ => 0, fun _ => 1} := by
    intro y hy
    have : 0 ≤ y () ∧ y () ≤ 1 := by
      by_contra hc; exact hy (Nat1D.f_out hc)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (show y () = 0 ∨ y () = 1 by omega) with h0 | h0
    · left; funext u; cases u; exact h0
    · right; funext u; cases u; exact h0
  exact Nat1D.not_mnatgs ((h Nat1D.f Nat1D.f_ce ⟨fun _ => 0, by
    show Nat1D.f _ ≠ ⊤; rw [Nat1D.f_in (x := fun _ => 0) (by simp)]; exact WithTop.coe_ne_top⟩
    ((Set.toFinite _).subset hdom)).2.mp Nat1D.f_mnat)

#print axioms solution
