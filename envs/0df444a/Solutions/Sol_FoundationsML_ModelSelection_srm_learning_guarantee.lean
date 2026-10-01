-- Prove2me | solution 1 for FoundationsML.ModelSelection.srm_learning_guarantee
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:59:58.102324+00:00
-- url     : https://prove2.me/submissions/67fb12be-4538-4d03-96ea-cbd2eaeb9ac7

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError
import Definitions.Def_FoundationsML_ModelSelection_RademacherComplexity
import Definitions.Def_FoundationsML_ModelSelection_LeastIndex

open FoundationsML.ModelSelection MeasureTheory in
/-- With samples of size `0`, every Rademacher complexity is `0`. -/
theorem rademacher_zero_efc3 {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    (G : Set (Z → ℝ)) : RademacherComplexity D G 0 = 0 := by
  unfold RademacherComplexity EmpiricalRademacherComplexity
  simp

open FoundationsML.ModelSelection MeasureTheory in
set_option linter.unusedVariables false in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] (c : X → ℝ) (Hk : ℕ → Set (X → ℝ))
    (hNested : ∀ k, 1 ≤ k → Hk k ⊆ Hk (k + 1))
    (m : ℕ) (hSRM : (Fin m → X) → (X → ℝ))
    (hSRM_mem : ∀ S, ∃ k, 1 ≤ k ∧ hSRM S ∈ Hk k)
    (hSRM_min : ∀ S, ∀ k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S c (hSRM S) + RademacherComplexity D (Hk (LeastIndex Hk (hSRM S))) m +
          Real.sqrt (Real.log (LeastIndex Hk (hSRM S)) / m) ≤
        EmpiricalError S c h + RademacherComplexity D (Hk k) m + Real.sqrt (Real.log k / m))
    (hHne : (⋃ k ≥ 1, Hk k).Nonempty)
    (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (hSRM S) ≤
        sInf ((fun h => GeneralizationError D c h +
            2 * RademacherComplexity D (Hk (LeastIndex Hk h)) m +
            Real.sqrt (Real.log (LeastIndex Hk h) / m)) '' (⋃ k ≥ 1, Hk k)) +
        Real.sqrt (2 * Real.log (3 / δ) / m)}).toReal) := by
  intro H
  -- X = Unit, D = dirac, c = 0, the bad hypothesis is 1, sample size m = 0
  let c : Unit → ℝ := fun _ => 0
  let b : Unit → ℝ := fun _ => 1
  let Hk : ℕ → Set (Unit → ℝ) := fun _ => {c, b}
  have hGc : GeneralizationError (Measure.dirac ()) c c = 0 := by
    simp [GeneralizationError]
  have hGb : GeneralizationError (Measure.dirac ()) c b = 1 := by
    simp [GeneralizationError, b, c]
  have hEmp : ∀ (S : Fin 0 → Unit) (h : Unit → ℝ), EmpiricalError S c h = 0 := by
    intro S h; simp [EmpiricalError]
  have key := H (X := Unit) (Measure.dirac ()) c Hk (fun _ _ => le_rfl) 0 (fun _ => b)
    (fun _ => ⟨1, le_rfl, by simp [Hk]⟩)
    (fun S k _ h _ => by simp [hEmp, rademacher_zero_efc3])
    ⟨c, Set.mem_iUnion₂.2 ⟨1, le_rfl, by simp [Hk]⟩⟩ (1 / 2) (by norm_num)
  have hempty : {S : Fin 0 → Unit | GeneralizationError (Measure.dirac ()) c b ≤
        sInf ((fun h => GeneralizationError (Measure.dirac ()) c h +
            2 * RademacherComplexity (Measure.dirac ()) (Hk (LeastIndex Hk h)) 0 +
            Real.sqrt (Real.log (LeastIndex Hk h) / ((0 : ℕ) : ℝ))) '' (⋃ k ≥ 1, Hk k)) +
        Real.sqrt (2 * Real.log (3 / (1 / 2 : ℝ)) / ((0 : ℕ) : ℝ))} = ∅ := by
    ext S
    refine ⟨fun hS => ?_, fun hS => hS.elim⟩
    change (_ : ℝ) ≤ (_ : ℝ) + (_ : ℝ) at hS
    have hsInf : sInf ((fun h => GeneralizationError (Measure.dirac ()) c h +
            2 * RademacherComplexity (Measure.dirac ()) (Hk (LeastIndex Hk h)) 0 +
            Real.sqrt (Real.log (LeastIndex Hk h) / ((0 : ℕ) : ℝ))) '' (⋃ k ≥ 1, Hk k)) ≤ 0 := by
      have hmem : (0 : ℝ) ∈ ((fun h => GeneralizationError (Measure.dirac ()) c h +
            2 * RademacherComplexity (Measure.dirac ()) (Hk (LeastIndex Hk h)) 0 +
            Real.sqrt (Real.log (LeastIndex Hk h) / ((0 : ℕ) : ℝ))) '' (⋃ k ≥ 1, Hk k)) := by
        refine ⟨c, Set.mem_iUnion₂.2 ⟨1, le_rfl, by simp [Hk]⟩, ?_⟩
        simp [hGc, rademacher_zero_efc3]
      refine csInf_le ⟨0, ?_⟩ hmem
      rintro y ⟨h, -, rfl⟩
      have : 0 ≤ GeneralizationError (Measure.dirac ()) c h := ENNReal.toReal_nonneg
      simp only [rademacher_zero_efc3, Nat.cast_zero, div_zero, Real.sqrt_zero]
      linarith
    have h2 : Real.sqrt (2 * Real.log (3 / (1 / 2 : ℝ)) / ((0 : ℕ) : ℝ)) = 0 := by simp
    rw [hGb, h2] at hS
    linarith
  rw [hempty] at key
  simp at key
  norm_num at key
