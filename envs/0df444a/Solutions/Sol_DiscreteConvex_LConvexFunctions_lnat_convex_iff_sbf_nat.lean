-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctions.lnat_convex_iff_sbf_nat
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T06:17:03.424165+00:00
-- url     : https://prove2.me/submissions/9a8d6f67-cde1-4758-a8f6-3bb65fc93554

import Definitions.Def_DiscreteConvex_LConvexFunctions_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctions_SBFNat
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ
import Mathlib.Tactic.Linarith

open DiscreteConvex.LConvexFunctions

namespace LNaturalTranslation
variable {V : Type*}

lemma lifted_translation (g : (V → ℤ) → WithTop ℝ) : TRF (LiftedFunctionL g) := by
  refine ⟨0,?_⟩
  intro p
  simp only [LiftedFunctionL,Pi.add_apply,Pi.one_apply,WithTop.coe_zero,add_zero]
  congr 1
  funext v
  omega

lemma from_lift (g : (V → ℤ) → WithTop ℝ) (hg : SBF (LiftedFunctionL g)) : SBFNat g := by
  intro p q α hα
  let x : Option V → ℤ := fun o => o.elim 0 p
  let y : Option V → ℤ := fun o => o.elim α (fun v => q v+α)
  have hx : LiftedFunctionL g x = g p := by simp [LiftedFunctionL,x]
  have hy : LiftedFunctionL g y = g q := by simp [LiftedFunctionL,y]
  have hsup : LiftedFunctionL g (x ⊔ y) = g (fun v => max (p v-α) (q v)) := by
    apply congrArg g
    funext v
    simp only [LiftedFunctionL,Pi.sup_apply,x,y,Option.elim_none,Option.elim_some]
    omega
  have hinf : LiftedFunctionL g (x ⊓ y) = g (fun v => min (p v) (q v+α)) := by
    apply congrArg g
    funext v
    simp only [LiftedFunctionL,Pi.inf_apply,x,y,Option.elim_none,Option.elim_some]
    omega
  simpa only [hx,hy,hsup,hinf] using hg x y

lemma to_lift_ordered (g : (V → ℤ) → WithTop ℝ) (hg : SBFNat g)
    (x y : Option V → ℤ) (hxy : x none ≤ y none) :
    LiftedFunctionL g (x ⊔ y) + LiftedFunctionL g (x ⊓ y) ≤
      LiftedFunctionL g x + LiftedFunctionL g y := by
  let p : V → ℤ := fun v => x (some v)-x none
  let q : V → ℤ := fun v => y (some v)-y none
  let α := y none-x none
  have hα : 0 ≤ α := by dsimp [α]; omega
  have hsup : LiftedFunctionL g (x ⊔ y) = g (fun v => max (p v-α) (q v)) := by
    apply congrArg g
    funext v
    simp only [LiftedFunctionL,Pi.sup_apply,p,q,α]
    omega
  have hinf : LiftedFunctionL g (x ⊓ y) = g (fun v => min (p v) (q v+α)) := by
    apply congrArg g
    funext v
    simp only [LiftedFunctionL,Pi.inf_apply,p,q,α]
    omega
  rw [hsup,hinf]
  exact hg p q α hα

lemma to_lift (g : (V → ℤ) → WithTop ℝ) (hg : SBFNat g) : SBF (LiftedFunctionL g) := by
  intro x y
  rcases le_total (x none) (y none) with h | h
  · exact to_lift_ordered g hg x y h
  · simpa only [sup_comm,inf_comm,add_comm] using to_lift_ordered g hg y x h

end LNaturalTranslation

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℤ) → WithTop ℝ) (hg : (DomZ g).Nonempty) :
    LNaturalConvex g ↔ SBFNat g := by
  constructor
  · intro h
    exact LNaturalTranslation.from_lift g h.1
  · intro h
    exact ⟨LNaturalTranslation.to_lift g h,LNaturalTranslation.lifted_translation g⟩

#print axioms LNaturalTranslation.from_lift
#print axioms LNaturalTranslation.to_lift
#print axioms solution
