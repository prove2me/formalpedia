-- Prove2me | solution 1 for FoundationsML.Boosting.ensemble_rademacher_margin_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T19:11:01.494997+00:00
-- url     : https://prove2.me/submissions/f8349d30-484c-432f-bbe1-09cd4fcb65f7

import Mathlib
import Definitions.Def_FoundationsML_Boosting_MarginGeneralizationError
import Definitions.Def_FoundationsML_Boosting_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Boosting_RademacherComplexity
import Definitions.Def_FoundationsML_Boosting_ConvHull

open MeasureTheory FoundationsML.Boosting in
/-- Counterexample instance: m = 0, X = Unit, H = {0}, D = dirac ((),0), ρ = 1, δ = 1/2. -/
theorem cex_c45a1ceb :
    ¬ ((1 - (1/2 : ℝ)) ≤ (Measure.pi (fun _ : Fin 0 => (Measure.dirac (((), (0:ℝ)) : Unit × ℝ)))
      {S : Fin 0 → Unit × ℝ | ∀ h ∈ ConvHull ({0} : Set (Unit → ℝ)),
        (MarginGeneralizationError (Measure.dirac (((), (0:ℝ)) : Unit × ℝ)) h ≤
           EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / 1) * RademacherComplexity ((Measure.dirac (((), (0:ℝ)) : Unit × ℝ)).map Prod.fst)
               ({0} : Set (Unit → ℝ)) 0 +
             Real.sqrt (Real.log (1 / (1/2)) / (2 * ((0:ℕ):ℝ)))) ∧
        (MarginGeneralizationError (Measure.dirac (((), (0:ℝ)) : Unit × ℝ)) h ≤
           EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / 1) * EmpiricalRademacherComplexity ({0} : Set (Unit → ℝ)) (fun i => (S i).1) +
             3 * Real.sqrt (Real.log (2 / (1/2)) / (2 * ((0:ℕ):ℝ))))}).toReal) := by
  have hmem : (0 : Unit → ℝ) ∈ ConvHull ({0} : Set (Unit → ℝ)) :=
    ⟨1, fun _ => 0, fun _ => 0, le_refl _, fun _ => le_refl _, fun _ => rfl, by simp, by
      funext x; simp⟩
  have hE : ∀ {Z : Type} (G : Set (Z → ℝ)) (S : Fin 0 → Z),
      EmpiricalRademacherComplexity G S = 0 := by
    intro Z G S; unfold EmpiricalRademacherComplexity; simp
  have hset : {S : Fin 0 → Unit × ℝ | ∀ h ∈ ConvHull ({0} : Set (Unit → ℝ)),
        (MarginGeneralizationError (Measure.dirac (((), (0:ℝ)) : Unit × ℝ)) h ≤
           EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / 1) * RademacherComplexity ((Measure.dirac (((), (0:ℝ)) : Unit × ℝ)).map Prod.fst)
               ({0} : Set (Unit → ℝ)) 0 +
             Real.sqrt (Real.log (1 / (1/2)) / (2 * ((0:ℕ):ℝ)))) ∧
        (MarginGeneralizationError (Measure.dirac (((), (0:ℝ)) : Unit × ℝ)) h ≤
           EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / 1) * EmpiricalRademacherComplexity ({0} : Set (Unit → ℝ)) (fun i => (S i).1) +
             3 * Real.sqrt (Real.log (2 / (1/2)) / (2 * ((0:ℕ):ℝ))))} = ∅ := by
    ext S
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hall
    have h1 := (hall 0 hmem).1
    have hR : RademacherComplexity ((Measure.dirac (((), (0:ℝ)) : Unit × ℝ)).map Prod.fst)
        ({0} : Set (Unit → ℝ)) 0 = 0 := by
      unfold RademacherComplexity; simp [hE]
    rw [hR] at h1
    simp [MarginGeneralizationError, EmpiricalMarginLoss] at h1
    linarith
  rw [hset]; simp
  norm_num

open MeasureTheory FoundationsML.Boosting in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hDfst : Measurable (Prod.fst : X × ℝ → X))
    (H : Set (X → ℝ)) (hHmeas : ∀ h ∈ ConvHull H, Measurable h)
    (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ ConvHull H,
        (MarginGeneralizationError D h ≤
           EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / ρ) * RademacherComplexity (D.map Prod.fst) H m +
             Real.sqrt (Real.log (1 / δ) / (2 * m))) ∧
        (MarginGeneralizationError D h ≤
           EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
             (2 / ρ) * EmpiricalRademacherComplexity H (fun i => (S i).1) +
             3 * Real.sqrt (Real.log (2 / δ) / (2 * m)))}).toReal) := by
  intro hall
  exact cex_c45a1ceb (hall (X := Unit) (Measure.dirac (((), (0:ℝ)) : Unit × ℝ)) measurable_fst
    ({0} : Set (Unit → ℝ)) (fun h _ => measurable_of_countable h) 0 1 one_pos (1/2) (by norm_num))
