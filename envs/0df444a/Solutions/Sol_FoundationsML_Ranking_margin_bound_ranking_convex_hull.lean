-- Prove2me | solution 1 for FoundationsML.Ranking.margin_bound_ranking_convex_hull
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T19:22:41.810762+00:00
-- url     : https://prove2.me/submissions/3bfe9ee2-5e8d-4edd-976a-ca6434c4d98a

import Mathlib
import Definitions.Def_FoundationsML_Ranking_GeneralizationError
import Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Ranking_RademacherComplexity
import Definitions.Def_FoundationsML_Ranking_ConvHull

open MeasureTheory in
open FoundationsML.Ranking in
/-- At sample size `m = 0` every complexity term vanishes (division by `m = 0`), so the bound
demands `R(h) ≤ 0`. Counterexample: `X = Unit`, `D = dirac ((), ())`, `f = 1`, `H = {0}`,
`ρ = 1`, `δ = 1/2`, `h = 0`, where `R(0) = 1`. -/
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure (X × X)) [IsProbabilityMeasure D]
    (f : X × X → ℝ) (hf : ∀ p, f p = 1 ∨ f p = -1) (H : Set (X → ℝ))
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ ConvHull H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (RademacherComplexity (Measure.map Prod.fst D) H m +
              RademacherComplexity (Measure.map Prod.snd D) H m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro hall
  have key := hall (X := Unit) (Measure.dirac ((), ())) (fun _ => (1:ℝ))
    (fun _ => Or.inl rfl) ({fun _ => 0} : Set (Unit → ℝ)) 1 one_pos 0 (1/2) (by norm_num)
  have hR : ∀ (μ : Measure Unit), RademacherComplexity μ ({fun _ => 0} : Set (Unit → ℝ)) 0 = 0 := by
    intro μ
    unfold RademacherComplexity EmpiricalRademacherComplexity
    simp
  have hmem : (fun _ : Unit => (0:ℝ)) ∈ ConvHull ({fun _ => 0} : Set (Unit → ℝ)) :=
    ⟨1, fun _ => 1, fun _ => fun _ => 0, fun _ => rfl, fun _ => zero_le_one, by simp, by simp⟩
  have hempty : {S : Fin 0 → Unit × Unit | ∀ h ∈ ConvHull ({fun _ => 0} : Set (Unit → ℝ)),
        GeneralizationError (Measure.dirac ((), ())) (fun _ => (1:ℝ)) h ≤
          EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) (fun _ => (1:ℝ)) h +
            (2 / (1:ℝ)) * (RademacherComplexity (Measure.map Prod.fst (Measure.dirac ((), ()) : Measure (Unit × Unit))) {fun _ => 0} 0 +
              RademacherComplexity (Measure.map Prod.snd (Measure.dirac ((), ()) : Measure (Unit × Unit))) {fun _ => 0} 0) +
            Real.sqrt (Real.log (1 / (1/2 : ℝ)) / (2 * ((0 : ℕ) : ℝ)))} = ∅ := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
    refine ⟨_, hmem, ?_⟩
    try rw [hR, hR]
    unfold GeneralizationError EmpiricalMarginLoss
    simp [hR]
  rw [hempty] at key
  simp at key
  norm_num at key
