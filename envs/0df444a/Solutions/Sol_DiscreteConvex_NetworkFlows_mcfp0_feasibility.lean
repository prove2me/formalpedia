-- Prove2me | solution 1 for DiscreteConvex.NetworkFlows.mcfp0_feasibility
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:18:23.679786+00:00
-- url     : https://prove2.me/submissions/00fd8fe4-ac4f-4158-9f54-eadb4c9312f5

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlows_CutCapacity
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerUpper
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerLower

open DiscreteConvex.NetworkFlows

/-- A single self-loop on a single vertex has no arc in any cut. -/
lemma loop_deltaPlus (X : Finset Unit) :
    DeltaPlus (fun _ : Unit => ()) (fun _ : Unit => ()) X = ∅ := by
  unfold DeltaPlus; ext a; simp

lemma loop_deltaMinus (X : Finset Unit) :
    DeltaMinus (fun _ : Unit => ()) (fun _ : Unit => ()) X = ∅ := by
  unfold DeltaMinus; ext a; simp

theorem solution : ¬ (∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (x : V → ℝ),
    ((∃ ξ : A → ℝ, FeasibleFlowMCFP0 tail head cUpper cLower x ξ) ↔
      ((∀ X : Finset V,
          ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ CutCapacity tail head cUpper cLower X) ∧
        (∑ v : V, x v) = 0)) ∧
    (IsIntegerUpper cUpper → IsIntegerLower cLower → (∀ v : V, ∃ n : ℤ, (n : ℝ) = x v) →
      (∃ ξ : A → ℝ, FeasibleFlowMCFP0 tail head cUpper cLower x ξ) →
      ∃ ξ : A → ℤ, FeasibleFlowMCFP0 tail head cUpper cLower x (fun a => (ξ a : ℝ)))) := by
  intro h
  have h1 := (@h Unit Unit _ _ _ (fun _ => ()) (fun _ => ()) (fun _ => ((0 : ℝ) : WithTop ℝ))
    (fun _ => ((1 : ℝ) : WithBot ℝ)) (fun _ => 0)).1
  have hcond : (∀ X : Finset Unit,
      ((∑ v ∈ X, (fun _ : Unit => (0 : ℝ)) v : ℝ) : WithTop ℝ) ≤
        CutCapacity (fun _ : Unit => ()) (fun _ : Unit => ()) (fun _ => ((0 : ℝ) : WithTop ℝ))
          (fun _ => ((1 : ℝ) : WithBot ℝ)) X) ∧ (∑ v : Unit, (fun _ : Unit => (0 : ℝ)) v) = 0 := by
    refine ⟨fun X => ?_, by simp⟩
    unfold CutCapacity
    rw [loop_deltaPlus, loop_deltaMinus]
    simp [UpperCapOf, NegLowerCapOf]
  obtain ⟨ξ, hξ, -⟩ := h1.mpr hcond
  obtain ⟨hlo, hhi⟩ := hξ ()
  have a1 : (1 : ℝ) ≤ ξ () := WithBot.coe_le_coe.mp hlo
  have a2 : ξ () ≤ 0 := WithTop.coe_le_coe.mp hhi
  linarith

#print axioms solution
