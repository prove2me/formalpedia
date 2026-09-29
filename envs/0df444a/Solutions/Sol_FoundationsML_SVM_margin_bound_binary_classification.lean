-- Prove2me | solution 1 for FoundationsML.SVM.margin_bound_binary_classification
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T14:20:20.666671+00:00
-- url     : https://prove2.me/submissions/144948ee-8a7a-4ce6-bb35-f3730b3b4f3c

import Mathlib
import Definitions.Def_FoundationsML_SVM_MarginGeneralizationError
import Definitions.Def_FoundationsML_SVM_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_SVM_RademacherComplexity

/-! Disproof of 6f2e8ca2 `FoundationsML.SVM.margin_bound_binary_classification`.

The statement puts no lower bound on the sample size `m`. At `m = 0`, every sample-dependent
quantity on the right-hand side is zero in Lean. `EmpiricalMarginLoss` is `(1/0) * (empty sum)`.
The empirical Rademacher complexity is a supremum of `(1/0) * (empty sum) = 0`, so it is `0`,
and so is its expectation `RademacherComplexity`. Both square-root terms are `√(c / 0) = √0 = 0`.

Take `X = Unit`, `D = δ_{((), 1)}`, `H = {0}`, `ρ = 1`, `δ = 1/2`. For `h = 0` the generalization
error is `D {p | p.2 * 0 ≤ 0} = D univ = 1`, which is not `≤ 0`. So the event is empty, its
probability is `0`, and `1 - δ = 1/2 ≤ 0` fails. -/

set_option autoImplicit false

open MeasureTheory

namespace SVMDis58

open FoundationsML.SVM

/-- At sample size `0` the empirical Rademacher complexity vanishes. -/
theorem erc_zero {Z : Type} (G : Set (Z → ℝ)) (S : Fin 0 → Z) :
    EmpiricalRademacherComplexity G S = 0 := by
  unfold EmpiricalRademacherComplexity
  simp

/-- At sample size `0` the Rademacher complexity vanishes. -/
theorem rc_zero {Z : Type} [MeasurableSpace Z] (D : Measure Z) (G : Set (Z → ℝ)) :
    RademacherComplexity D G 0 = 0 := by
  unfold RademacherComplexity
  simp [erc_zero]

/-- At sample size `0` the empirical margin loss vanishes. -/
theorem eml_zero {X : Type} (ρ : ℝ) (S : Fin 0 → X) (y : Fin 0 → ℝ) (h : X → ℝ) :
    EmpiricalMarginLoss ρ S y h = 0 := by
  unfold EmpiricalMarginLoss
  simp

/-- The zero hypothesis has generalization error `1` under any probability measure. -/
theorem mge_zero {X : Type} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D] :
    MarginGeneralizationError D (fun _ => (0 : ℝ)) = 1 := by
  unfold MarginGeneralizationError
  simp

end SVMDis58

open FoundationsML.SVM in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hDfst : Measurable (Prod.fst : X × ℝ → X))
    (H : Set (X → ℝ)) (hHmeas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        (MarginGeneralizationError D h ≤
           EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / ρ) * RademacherComplexity (D.map Prod.fst) H m +
             Real.sqrt (Real.log (1 / δ) / (2 * m))) ∧
        (MarginGeneralizationError D h ≤
           EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / ρ) * EmpiricalRademacherComplexity H (fun i => (S i).1) +
             3 * Real.sqrt (Real.log (2 / δ) / (2 * m)))}).toReal) := by
  intro hT
  have hmeas : ∀ h ∈ ({fun _ => (0 : ℝ)} : Set (Unit → ℝ)), Measurable h := by
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact measurable_const
  have key := @hT Unit _ (Measure.dirac ((), (1 : ℝ))) _ measurable_fst
    {fun _ => (0 : ℝ)} hmeas 0 1 one_pos (1 / 2) (by norm_num)
  have hempty : {S : Fin 0 → Unit × ℝ | ∀ h ∈ ({fun _ => (0 : ℝ)} : Set (Unit → ℝ)),
        (MarginGeneralizationError (Measure.dirac ((), (1 : ℝ))) h ≤
           EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / 1) * RademacherComplexity ((Measure.dirac ((), (1 : ℝ))).map Prod.fst)
               ({fun _ => (0 : ℝ)} : Set (Unit → ℝ)) 0 +
             Real.sqrt (Real.log (1 / (1 / 2)) / (2 * ((0 : ℕ) : ℝ)))) ∧
        (MarginGeneralizationError (Measure.dirac ((), (1 : ℝ))) h ≤
           EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / 1) * EmpiricalRademacherComplexity ({fun _ => (0 : ℝ)} : Set (Unit → ℝ))
               (fun i => (S i).1) +
             3 * Real.sqrt (Real.log (2 / (1 / 2)) / (2 * ((0 : ℕ) : ℝ))))} = ∅ := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hS
    have h1 := (hS (fun _ => (0 : ℝ)) (Set.mem_singleton _)).1
    rw [SVMDis58.mge_zero, SVMDis58.eml_zero, SVMDis58.rc_zero] at h1
    norm_num at h1
  rw [hempty, measure_empty, ENNReal.toReal_zero] at key
  norm_num at key
