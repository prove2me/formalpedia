-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.polyhedral_lnat_operations_and_restrictions
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:27:06.929133+00:00
-- url     : https://prove2.me/submissions/a4b1e9c1-ed19-4aa1-ad18-fd007a61db28

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvexR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ProjectionR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SeparablePerturbInfConvR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IntervalRestrictR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_RestrictionR

open Classical
open scoped Pointwise

namespace DisPLN
open DiscreteConvex.LConvexFunctionsC

noncomputable def g : (Unit → ℝ) → WithTop ℝ := fun p => if p () = 0 then 0 else ⊤

noncomputable def psi : Unit → ℝ → WithTop ℝ := fun _ s => ((-(s ^ 2) : ℝ) : WithTop ℝ)

lemma hg : LNaturalConvexR g := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro p q
    simp only [LiftedFunctionLR, g]
    by_cases hp : p (some ()) - p none = 0
    · by_cases hq : q (some ()) - q none = 0
      · have hp' : p (some ()) = p none := by linarith
        have hq' : q (some ()) = q none := by linarith
        have h1 : (p ⊔ q) (some ()) - (p ⊔ q) none = 0 := by
          simp only [Pi.sup_apply, hp', hq', sub_self]
        have h2 : (p ⊓ q) (some ()) - (p ⊓ q) none = 0 := by
          simp only [Pi.inf_apply, hp', hq', sub_self]
        rw [if_pos hp, if_pos hq, if_pos h1, if_pos h2]
      · rw [if_neg hq]; simp
    · rw [if_neg hp]; simp
  · intro p α
    simp [LiftedFunctionLR, g]

lemma conv_eq (p : Unit → ℝ) :
    SeparablePerturbInfConvR g psi p = ((-(p () ^ 2) : ℝ) : WithTop ℝ) := by
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨0, ?_⟩
    simp [g, psi]
  · rintro L ⟨q, rfl⟩
    by_cases hq : q () = 0
    · have : q = 0 := funext fun u => by cases u; exact hq
      subst this
      simp [g, psi]
    · simp [g, hq]

lemma not_lnat : ¬ LNaturalConvexR (SeparablePerturbInfConvR g psi) := by
  intro h
  have := h.1 (fun o => if o = none then 1 else 0) (fun o => if o = none then 0 else 1)
  simp only [LiftedFunctionLR, conv_eq] at this
  have e1 : ((fun o : Option Unit => if o = none then (1:ℝ) else 0) ⊔
      (fun o => if o = none then (0:ℝ) else 1)) = fun _ => 1 := by
    funext o; cases o <;> simp
  have e2 : ((fun o : Option Unit => if o = none then (1:ℝ) else 0) ⊓
      (fun o => if o = none then (0:ℝ) else 1)) = fun _ => 0 := by
    funext o; cases o <;> simp
  rw [e1, e2] at this
  simp only [reduceCtorEq, if_true, if_false] at this
  have h' : ((-1 + -1 : ℝ) : WithTop ℝ) ≥ ((0 + 0 : ℝ) : WithTop ℝ) := by
    push_cast; norm_num at this ⊢; exact this
  have := WithTop.coe_le_coe.mp h'
  norm_num at this

end DisPLN

open DiscreteConvex.LConvexFunctionsC in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g g1 g2 : (V → ℝ) → WithTop ℝ)
    (_hg : LNaturalConvexR g) (_hg1 : LNaturalConvexR g1) (_hg2 : LNaturalConvexR g2),
    ((∀ lam : ℝ, 0 < lam → LNaturalConvexR (fun p => PosScalarMul lam (g p))) ∧
     (∀ a : V → ℝ, ∀ beta : ℝ, beta ≠ 0 →
       LNaturalConvexR (fun p => g (fun v => a v + beta * p v))) ∧
     (∀ x : V → ℝ, LNaturalConvexR (LinearWeightR g (fun v => - x v))) ∧
     (∀ U : Set V, (DomR (ProjectionR g U)).Nonempty → LNaturalConvexR (ProjectionR g U)) ∧
     (∀ psi : V → ℝ → WithTop ℝ, (DomR (SeparablePerturbInfConvR g psi)).Nonempty →
        LNaturalConvexR (SeparablePerturbInfConvR g psi)) ∧
     ((DomR (fun p => g1 p + g2 p)).Nonempty → LNaturalConvexR (fun p => g1 p + g2 p))) ∧
    (∀ a b : V → WithBot (WithTop ℝ), (DomR (IntervalRestrictR g a b)).Nonempty →
      LNaturalConvexR (IntervalRestrictR g a b)) ∧
    (∀ U : Finset V, (DomR (RestrictionR g U)).Nonempty → LNaturalConvexR (RestrictionR g U))) := by
  intro h
  have hd : (DomR (SeparablePerturbInfConvR DisPLN.g DisPLN.psi)).Nonempty :=
    ⟨0, by simp [DomR, DisPLN.conv_eq]⟩
  exact DisPLN.not_lnat
    ((h (V := Unit) DisPLN.g DisPLN.g DisPLN.g DisPLN.hg DisPLN.hg DisPLN.hg).1.2.2.2.2.1
      DisPLN.psi hd)
