-- Prove2me | solution 1 for FeinbergPOMDP.WStar.theorem_3_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:45:19.767354+00:00
-- url     : https://prove2.me/submissions/3a3fa09b-eaa0-4b7e-81d0-335ec9c8df6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Theorems.Thm_FeinbergPOMDP_WStar_theorem_3_4
import Theorems.Thm_FeinbergPOMDP_WStar_theorem_3_7

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE FeinbergPOMDP.WStar

theorem solution {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [StandardBorelSpace X] [Nonempty X]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (lower α : ℝ) (f : X → A → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (hDP : (0 ≤ α ∧ α < 1) ∨
      ((∀ (x : X) (a : A), (0 : EReal) ≤ (lower : EReal) + (f x a : EReal)) ∧
        0 ≤ α ∧ α ≤ 1))
    (hK : KInfCompact f)
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q)) :
    (∀ K : ℝ, (∀ (x : X) (a : A), (K : EReal) ≤ (lower : EReal) + (f x a : EReal)) →
        ∀ (z : ProbabilityMeasure X) (a : A),
          (K : EReal) ≤ (lower : EReal) + (beliefCost f z a : EReal)) ∧
    KInfCompact (beliefCost f) ∧
    ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X,
      IsFilter P Q H → BeliefTransitionWeaklyContinuous P Q H := by
  obtain ⟨h1, h2⟩ := theorem_3_4 lower f hf hK
  exact ⟨h1, h2, (theorem_3_7 (Y := Y) P Q hP hQ).2.2⟩
