-- Prove2me | solution 1 for BalanceSpecification.real_inter_le_inter_add_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:36.519244+00:00
-- url     : https://prove2.me/submissions/531adb23-ec31-4a5e-ad5c-a5beec06344d

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]
omit [Fintype A] [DiscreteTopology A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A}
    (μ : Measure X.carrier) [IsFiniteMeasure μ] (B E C : Set X.carrier) :
    μ.real (B ∩ C) ≤ μ.real (E ∩ C) + μ.real (B ∆ E) := by
  have hsub : B ∩ C ⊆ (E ∩ C) ∪ (B ∆ E) := by
    rintro x ⟨hb, hc⟩
    by_cases he : x ∈ E
    · exact Or.inl ⟨he, hc⟩
    · exact Or.inr (Or.inl ⟨hb, he⟩)
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
end BalanceSpecification
