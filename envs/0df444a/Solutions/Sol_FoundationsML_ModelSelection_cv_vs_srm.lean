-- Prove2me | solution 1 for FoundationsML.ModelSelection.cv_vs_srm
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T19:55:24.372313+00:00
-- url     : https://prove2.me/submissions/c86b3e4d-0723-4915-bbb6-04f41abf2004

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError
import Definitions.Def_FoundationsML_ModelSelection_RademacherComplexity
import Definitions.Def_FoundationsML_ModelSelection_LeastIndex

open MeasureTheory FoundationsML.ModelSelection in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c : X → ℝ) (Hk : ℕ → Set (X → ℝ)) (m m1 m2 : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hm1 : (m1 : ℝ) = (1 - α) * m) (hm2 : (m2 : ℝ) = α * m)
    (hNested : ∀ k, 1 ≤ k → Hk k ⊆ Hk (k + 1))
    (hCV : (Fin m1 → X) → (Fin m2 → X) → (X → ℝ))
    (hSRM1 : (Fin m1 → X) → (X → ℝ))
    (hERMk : (Fin m1 → X) → ℕ → (X → ℝ))
    (hERMk_mem : ∀ S1 k, 1 ≤ k → hERMk S1 k ∈ Hk k)
    (hERMk_min : ∀ S1 k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S1 c (hERMk S1 k) ≤ EmpiricalError S1 c h)
    (hCV_eq : ∀ S1 S2, ∃ k, 1 ≤ k ∧ hCV S1 S2 = hERMk S1 k)
    (hCV_min : ∀ S1 S2, ∀ k, 1 ≤ k → EmpiricalError S2 c (hCV S1 S2) ≤ EmpiricalError S2 c (hERMk S1 k))
    (hCV_mem : ∀ S1 S2, ∃ k, 1 ≤ k ∧ hCV S1 S2 ∈ Hk k)
    (hSRM1_mem : ∀ S1, ∃ k, 1 ≤ k ∧ hSRM1 S1 ∈ Hk k)
    (hSRM1_min : ∀ S1, ∀ k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S1 c (hSRM1 S1) + RademacherComplexity D (Hk (LeastIndex Hk (hSRM1 S1))) m1 +
          Real.sqrt (Real.log (LeastIndex Hk (hSRM1 S1)) / m1) ≤
        EmpiricalError S1 c h + RademacherComplexity D (Hk k) m1 + Real.sqrt (Real.log k / m1))
    (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.prod (Measure.pi (fun _ : Fin m1 => D)) (Measure.pi (fun _ : Fin m2 => D))
      {p : (Fin m1 → X) × (Fin m2 → X) |
        GeneralizationError D c (hCV p.1 p.2) - GeneralizationError D c (hSRM1 p.1) ≤
          2 * Real.sqrt (Real.log
              (max (LeastIndex Hk (hCV p.1 p.2)) (LeastIndex Hk (hSRM1 p.1))) / (α * m)) +
          2 * Real.sqrt (Real.log (4 / δ) / (2 * α * m))}).toReal) := by
  intro H
  have := @H Unit _ (Measure.dirac ()) _ (fun _ => 0)
    (fun _ => {f : Unit → ℝ | f = (fun _ => 0) ∨ f = (fun _ => 1)}) 0 0 0 (1/2) (by norm_num) (by norm_num)
    (by simp) (by simp) (fun k _ => le_refl _)
    (fun _ _ => fun _ => 1) (fun _ => fun _ => 0) (fun _ _ => fun _ => 1)
    (fun _ _ _ => Or.inr rfl)
    (fun S1 k _ h _ => by simp [EmpiricalError])
    (fun _ _ => ⟨1, le_refl _, rfl⟩)
    (fun _ _ _ _ => le_refl _)
    (fun _ _ => ⟨1, le_refl _, Or.inr rfl⟩)
    (fun _ => ⟨1, le_refl _, Or.inl rfl⟩)
    (fun S1 k _ h _ => by simp [EmpiricalError])
    (1/2) (by norm_num)
  have hGE1 : GeneralizationError (Measure.dirac ()) (fun _ : Unit => (0:ℝ)) (fun _ => 1) = 1 := by
    simp [GeneralizationError]
  have hGE0 : GeneralizationError (Measure.dirac ()) (fun _ : Unit => (0:ℝ)) (fun _ => 0) = 0 := by
    simp [GeneralizationError]
  simp only [hGE1, hGE0, Nat.cast_zero, mul_zero, div_zero, Real.sqrt_zero] at this
  norm_num at this
