-- Prove2me | solution 1 for FoundationsML.Ranking.margin_bound_ranking
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T19:34:08.203136+00:00
-- url     : https://prove2.me/submissions/5d898d01-97b4-40b4-b820-a394b3873e4c

import Mathlib
import Definitions.Def_FoundationsML_Ranking_GeneralizationError
import Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Ranking_RademacherComplexity
import Definitions.Def_FoundationsML_Ranking_EmpiricalRademacherComplexity

open MeasureTheory FoundationsML.Ranking in
/-- Counterexample instance: m = 0, X = Unit, D = dirac ((),()), f = 1, H = {0}, ρ = 1, δ = 1/2. -/
theorem cex_642331be :
    ¬ ((1 - (1/2 : ℝ)) ≤ (Measure.pi (fun _ : Fin 0 => (Measure.dirac ((), ()) : Measure (Unit × Unit)))
      {S : Fin 0 → Unit × Unit | ∀ h ∈ ({fun _ => 0} : Set (Unit → ℝ)),
        GeneralizationError (Measure.dirac ((), ())) (fun _ => 1) h ≤
          EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) (fun i => (fun _ => (1:ℝ)) (S i)) h +
            (2 / 1) * (RademacherComplexity (Measure.map Prod.fst (Measure.dirac ((), ()))) ({fun _ => 0} : Set (Unit → ℝ)) 0 +
              RademacherComplexity (Measure.map Prod.snd (Measure.dirac ((), ()))) ({fun _ => 0} : Set (Unit → ℝ)) 0) +
            Real.sqrt (Real.log (1 / (1/2 : ℝ)) / (2 * (0:ℕ)))}).toReal) := by
  have hE : ∀ (S : Fin 0 → Unit), EmpiricalRademacherComplexity ({fun _ => 0} : Set (Unit → ℝ)) S = 0 := by
    intro S
    simp [EmpiricalRademacherComplexity]
  have hset : {S : Fin 0 → Unit × Unit | ∀ h ∈ ({fun _ => 0} : Set (Unit → ℝ)),
        GeneralizationError (Measure.dirac ((), ())) (fun _ => 1) h ≤
          EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) (fun i => (fun _ => (1:ℝ)) (S i)) h +
            (2 / 1) * (RademacherComplexity (Measure.map Prod.fst (Measure.dirac ((), ()))) ({fun _ => 0} : Set (Unit → ℝ)) 0 +
              RademacherComplexity (Measure.map Prod.snd (Measure.dirac ((), ()))) ({fun _ => 0} : Set (Unit → ℝ)) 0) +
            Real.sqrt (Real.log (1 / (1/2 : ℝ)) / (2 * (0:ℕ)))} = ∅ := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, Set.mem_empty_iff_false,
      iff_false, not_le]
    simp [GeneralizationError, EmpiricalMarginLoss, RademacherComplexity, hE]
  rw [hset]
  simp
  norm_num

open MeasureTheory FoundationsML.Ranking in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure (X × X)) [IsProbabilityMeasure D]
    (f : X × X → ℝ) (hf : ∀ p, f p = 1 ∨ f p = -1) (H : Set (X → ℝ))
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (RademacherComplexity (Measure.map Prod.fst D) H m +
              RademacherComplexity (Measure.map Prod.snd D) H m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (EmpiricalRademacherComplexity H (fun i => (S i).1) +
              EmpiricalRademacherComplexity H (fun i => (S i).2)) +
            3 * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal) := by
  intro hall
  exact cex_642331be (hall (X := Unit) (Measure.dirac ((), ())) (fun _ => 1)
    (fun _ => Or.inl rfl) ({fun _ => 0} : Set (Unit → ℝ)) 1 one_pos 0 (1/2) (by norm_num)).1
