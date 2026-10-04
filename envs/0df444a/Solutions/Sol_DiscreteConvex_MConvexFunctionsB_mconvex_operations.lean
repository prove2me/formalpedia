-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsB.mconvex_operations
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:44:45.693987+00:00
-- url     : https://prove2.me/submissions/a6ae0e6c-4ce1-4b9d-8b13-8ef32269b50f

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_PosScalarMul
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_LinearWeight
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SeparablePerturb
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_IntervalRestrict
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_Restriction

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.MConvexFunctionsB

namespace OpsCex

/-- The indicator (value `0`) of the line `x(true) + x(false) = 0`: an M-convex function. -/
noncomputable def f (x : Bool → ℤ) : WithTop ℝ :=
  if x true + x false = 0 then ((0 : ℝ) : WithTop ℝ) else ⊤

/-- `ψ = 0` on `{0, 3}` and `+∞` elsewhere: midpoint convex with a hole in its domain. -/
noncomputable def psi (x : ℤ) : WithTop ℝ :=
  if x = 0 ∨ x = 3 then ((0 : ℝ) : WithTop ℝ) else ⊤

noncomputable def phi : Bool → ℤ → WithTop ℝ := fun b => if b then psi else fun _ => 0

theorem mem_dom {x : Bool → ℤ} (hx : x ∈ DomZ f) : x true + x false = 0 := by
  by_contra h; exact hx (by simp [f, h])

theorem f_val {x : Bool → ℤ} (h : x true + x false = 0) : f x = ((0 : ℝ) : WithTop ℝ) := by
  simp [f, h]

theorem f_exc : MExchangeAxiom f := by
  intro x hx y hy u hu
  have h1 := mem_dom hx
  have h2 := mem_dom hy
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  refine ⟨!u, ?_, ?_⟩
  · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
    cases u <;> simp at hu ⊢ <;> omega
  · rw [f_val h1, f_val h2, f_val (by cases u <;> simp [CharVec] <;> omega),
      f_val (by cases u <;> simp [CharVec] <;> omega)]

theorem psi_dcu : DiscreteConvexUnivariate psi := by
  refine ⟨⟨0, by simp [psi]⟩, fun x => ?_⟩
  by_cases h1 : x = 0 ∨ x = 3
  · by_cases h2 : x + 2 = 0 ∨ x + 2 = 3
    · exfalso; omega
    · have : psi (x + 2) = ⊤ := by simp only [psi]; rw [if_neg h2]
      rw [this]; simp
  · have : psi x = ⊤ := by simp only [psi]; rw [if_neg h1]
    rw [this]; simp

theorem phi_dcu : ∀ v, DiscreteConvexUnivariate (phi v) := by
  intro v
  cases v
  · refine ⟨⟨0, by simp [phi]⟩, fun x => ?_⟩
    simp [phi]
  · simpa [phi] using psi_dcu

theorem sp_val (x : Bool → ℤ) :
    SeparablePerturb f phi x = f x + psi (x true) := by
  simp [SeparablePerturb, phi, add_comm]

theorem not_exc : ¬ MExchangeAxiom (SeparablePerturb f phi) := by
  intro h
  let x : Bool → ℤ := fun b => if b then 3 else -3
  let y : Bool → ℤ := fun _ => 0
  have hx : x ∈ DomZ (SeparablePerturb f phi) := by
    show SeparablePerturb f phi x ≠ ⊤
    rw [sp_val, f_val (by simp [x])]; simp [psi, x]
  have hy : y ∈ DomZ (SeparablePerturb f phi) := by
    show SeparablePerturb f phi y ≠ ⊤
    rw [sp_val, f_val (by simp [y])]; simp [psi, y]
  obtain ⟨v, hv, hineq⟩ := h x hx y hy true (by simp [SuppPos, x, y])
  cases v with
  | true => simp [SuppNeg, x, y] at hv
  | false =>
    have hl : SeparablePerturb f phi (fun w => x w - CharVec true w + CharVec false w) = ⊤ := by
      rw [sp_val]; simp [psi, x, CharVec]
    have h0 : SeparablePerturb f phi x + SeparablePerturb f phi y = ((0 : ℝ) : WithTop ℝ) := by
      rw [sp_val, sp_val, f_val (by simp [x]), f_val (by simp [y])]
      simp [psi, x, y]
    rw [hl, h0, top_add] at hineq
    exact WithTop.coe_ne_top (top_le_iff.mp hineq)

end OpsCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f),
    (∀ lam : ℝ, 0 < lam → MExchangeAxiom (fun x => PosScalarMul lam (f x))) ∧
    (∀ a : V → ℤ, MExchangeAxiom (fun x => f (fun v => a v - x v)) ∧
      MExchangeAxiom (fun x => f (fun v => a v + x v))) ∧
    (∀ p : V → ℝ, MExchangeAxiom (LinearWeight f p)) ∧
    (∀ phi : V → ℤ → WithTop ℝ, (∀ v, DiscreteConvexUnivariate (phi v)) →
      (DomZ (SeparablePerturb f phi)).Nonempty → MExchangeAxiom (SeparablePerturb f phi)) ∧
    (∀ a b : V → WithBot (WithTop ℤ), (DomZ (IntervalRestrict f a b)).Nonempty →
      MExchangeAxiom (IntervalRestrict f a b)) ∧
    (∀ U : Finset V, (DomZ (Restriction f U)).Nonempty → MExchangeAxiom (Restriction f U))) := by
  intro h
  refine OpsCex.not_exc ((h OpsCex.f OpsCex.f_exc).2.2.2.1 OpsCex.phi OpsCex.phi_dcu
    ⟨fun _ => 0, ?_⟩)
  show SeparablePerturb OpsCex.f OpsCex.phi (fun _ => 0) ≠ ⊤
  rw [OpsCex.sp_val, OpsCex.f_val (by simp)]
  simp [OpsCex.psi]

#print axioms solution
