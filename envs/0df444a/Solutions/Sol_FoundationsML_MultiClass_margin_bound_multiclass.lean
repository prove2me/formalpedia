-- Prove2me | solution 1 for FoundationsML.MultiClass.margin_bound_multiclass
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:01:24.013543+00:00
-- url     : https://prove2.me/submissions/3a85f05f-a623-47be-8521-4822a1a9c63a

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GeneralizationError
import Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_MultiClass_Proj1
import Definitions.Def_FoundationsML_MultiClass_RademacherComplexity

open MeasureTheory

namespace FoundationsML.MultiClass

/-- The zero scoring function has margin `0` everywhere. -/
theorem aux_mbm_margin_zero (x : Unit) (y : Fin 2) :
    MarginFunction (fun _ : Unit × Fin 2 => (0 : ℝ)) x y = 0 := by
  simp [MarginFunction, Real.iSup_const_zero]

/-- The zero scoring function misclassifies everything under `D = δ_()`. -/
theorem aux_mbm_generr :
    GeneralizationError (Measure.dirac ()) (fun _ : Unit => (0 : Fin 2))
      (fun _ : Unit × Fin 2 => (0 : ℝ)) = 1 := by
  unfold GeneralizationError
  simp [aux_mbm_margin_zero]

/-- With `m = 0` the empirical margin loss is `0`. -/
theorem aux_mbm_eml (S : Fin 0 → Unit) :
    EmpiricalMarginLoss 1 S (fun _ : Unit => (0 : Fin 2))
      (fun _ : Unit × Fin 2 => (0 : ℝ)) = 0 := by
  simp [EmpiricalMarginLoss]

/-- With `m = 0` the empirical Rademacher complexity is `0`. -/
theorem aux_mbm_erc (G : Set (Unit → ℝ)) (S : Fin 0 → Unit) :
    EmpiricalRademacherComplexity G S = 0 := by
  simp [EmpiricalRademacherComplexity, Real.iSup_const_zero]

theorem aux_mbm_rc (G : Set (Unit → ℝ)) :
    RademacherComplexity (Measure.dirac ()) G 0 = 0 := by
  unfold RademacherComplexity
  simp [aux_mbm_erc]

end FoundationsML.MultiClass

open FoundationsML.MultiClass

theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (k : ℕ) (hk : 2 ≤ k) (f : X → Fin k) (H : Set (X × Fin k → ℝ))
    (hHb : ∃ M : ℝ, ∀ h ∈ H, ∀ z : X × Fin k, |h z| ≤ M)
    (hHmeas : ∀ h ∈ H, ∀ y : Fin k, Measurable (fun x => h (x, y)))
    (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D f h ≤
        EmpiricalMarginLoss ρ S f h + (4 * (k : ℝ) / ρ) * RademacherComplexity D (Proj1 H) m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro Hall
  have h := Hall (X := Unit) (Measure.dirac ()) 2 le_rfl (fun _ => 0)
    {fun _ => (0 : ℝ)} ⟨0, by simp⟩ (by simp) 0 1 one_pos (1 / 2) (by norm_num)
  have hset : {S : Fin 0 → Unit | ∀ h ∈ ({fun _ => (0 : ℝ)} : Set (Unit × Fin 2 → ℝ)),
      GeneralizationError (Measure.dirac ()) (fun _ : Unit => (0 : Fin 2)) h ≤
        EmpiricalMarginLoss 1 S (fun _ : Unit => (0 : Fin 2)) h +
          (4 * ((2 : ℕ) : ℝ) / 1) *
            RademacherComplexity (Measure.dirac ())
              (Proj1 ({fun _ => (0 : ℝ)} : Set (Unit × Fin 2 → ℝ))) 0 +
          Real.sqrt (Real.log (1 / (1 / 2 : ℝ)) / (2 * ((0 : ℕ) : ℝ)))} = ∅ := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, Set.mem_empty_iff_false,
      iff_false, aux_mbm_generr, aux_mbm_eml, aux_mbm_rc]
    simp
  rw [hset] at h
  simp at h
  norm_num at h
