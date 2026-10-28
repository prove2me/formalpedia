-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.polyhedral_lconvex_basic_operations
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:27:36.185606+00:00
-- url     : https://prove2.me/submissions/ce93f619-8c22-476c-a0fb-89c79569ef8f

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ProjectionR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SeparablePerturbInfConvR

open Classical
open scoped Pointwise

namespace DisPLB
open DiscreteConvex.LConvexFunctionsC

noncomputable def g : (Fin 2 → ℝ) → WithTop ℝ := fun p => if p 0 = p 1 then 0 else ⊤

noncomputable def psi : Fin 2 → ℝ → WithTop ℝ := fun i s =>
  if i = 0 then ((-(s ^ 2) : ℝ) : WithTop ℝ) else (if s = 0 then 0 else ⊤)

lemma hg : SBFR g ∧ TRFR g := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro p q
    simp only [g]
    by_cases hp : p 0 = p 1
    · by_cases hq : q 0 = q 1
      · have h1 : (p ⊔ q) 0 = (p ⊔ q) 1 := by simp only [Pi.sup_apply, hp, hq]
        have h2 : (p ⊓ q) 0 = (p ⊓ q) 1 := by simp only [Pi.inf_apply, hp, hq]
        rw [if_pos hp, if_pos hq, if_pos h1, if_pos h2]
      · rw [if_neg hq]; simp
    · rw [if_neg hp]; simp
  · intro p α
    simp [g]

lemma conv_eq (p : Fin 2 → ℝ) :
    SeparablePerturbInfConvR g psi p = ((-((p 0 - p 1) ^ 2) : ℝ) : WithTop ℝ) := by
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨fun _ => p 1, ?_⟩
    simp [g, psi, Fin.sum_univ_two]
  · rintro L ⟨q, rfl⟩
    by_cases hq : q 0 = q 1
    · by_cases h1 : p 1 - q 1 = 0
      · have h1' : q 1 = p 1 := by linarith
        simp [g, psi, Fin.sum_univ_two, hq, h1']
      · simp [g, psi, Fin.sum_univ_two, h1]
    · simp [g, hq]

lemma not_sbfr : ¬ SBFR (SeparablePerturbInfConvR g psi) := by
  intro h
  have := h ![1, 0] ![0, 1]
  simp only [conv_eq] at this
  have e1 : ((![1, 0] : Fin 2 → ℝ) ⊔ ![0, 1]) 0 = 1 := by simp
  have e2 : ((![1, 0] : Fin 2 → ℝ) ⊔ ![0, 1]) 1 = 1 := by simp
  have e3 : ((![1, 0] : Fin 2 → ℝ) ⊓ ![0, 1]) 0 = 0 := by simp
  have e4 : ((![1, 0] : Fin 2 → ℝ) ⊓ ![0, 1]) 1 = 0 := by simp
  rw [e1, e2, e3, e4] at this
  have h' : ((-1 + -1 : ℝ) : WithTop ℝ) ≥ ((0 + 0 : ℝ) : WithTop ℝ) := by
    push_cast; norm_num at this ⊢; exact this
  have := WithTop.coe_le_coe.mp h'
  norm_num at this

end DisPLB

open DiscreteConvex.LConvexFunctionsC in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (g g1 g2 : (V → ℝ) → WithTop ℝ) (_hg : SBFR g ∧ TRFR g),
    (∀ lam : ℝ, 0 < lam →
      SBFR (fun p => PosScalarMul lam (g p)) ∧ TRFR (fun p => PosScalarMul lam (g p))) ∧
    (∀ a : V → ℝ, ∀ beta : ℝ, beta ≠ 0 →
      SBFR (fun p => g (fun v => a v + beta * p v)) ∧
      TRFR (fun p => g (fun v => a v + beta * p v))) ∧
    (∀ x : V → ℝ, SBFR (LinearWeightR g (fun v => - x v)) ∧ TRFR (LinearWeightR g (fun v => - x v))) ∧
    (∀ U : Set V, (DomR (ProjectionR g U)).Nonempty →
      SBFR (ProjectionR g U) ∧ TRFR (ProjectionR g U)) ∧
    (∀ psi : V → ℝ → WithTop ℝ, (DomR (SeparablePerturbInfConvR g psi)).Nonempty →
      SBFR (SeparablePerturbInfConvR g psi) ∧ TRFR (SeparablePerturbInfConvR g psi)) ∧
    ((DomR (fun p => g1 p + g2 p)).Nonempty → SBFR g1 → TRFR g1 → SBFR g2 → TRFR g2 →
      SBFR (fun p => g1 p + g2 p) ∧ TRFR (fun p => g1 p + g2 p))) := by
  intro h
  have hd : (DomR (SeparablePerturbInfConvR DisPLB.g DisPLB.psi)).Nonempty :=
    ⟨0, by simp [DomR, DisPLB.conv_eq]⟩
  exact DisPLB.not_sbfr
    ((h (V := Fin 2) DisPLB.g DisPLB.g DisPLB.g DisPLB.hg).2.2.2.2.1 DisPLB.psi hd).1
