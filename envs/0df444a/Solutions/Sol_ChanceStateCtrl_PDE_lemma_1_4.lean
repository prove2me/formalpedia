-- Prove2me | solution 1 for ChanceStateCtrl.PDE.lemma_1_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:18:36.184174+00:00
-- url     : https://prove2.me/submissions/ec5c5fd2-4ac0-47b9-a5a6-5024b6142b6b

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open ChanceStateCtrl.PDE
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

theorem solution {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (u : L2 D) (x : closure D) :
    Measurable (fun w => stateS Ainv f₀ φ u (ξ w) x) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin m) => stateS Ainv f₀ φ u z x) := by
    unfold stateS
    have h1 : Continuous (fun z : EuclideanSpace ℝ (Fin m) => u + f₀ + ∑ i, z i • φ i) := by
      refine continuous_const.add (continuous_finsetSum _ (fun i _ => ?_))
      exact (PiLp.continuous_apply 2 _ i).smul continuous_const
    exact (continuous_eval_const x).comp (Ainv.continuous.comp h1)
  exact hc.measurable.comp hξ
