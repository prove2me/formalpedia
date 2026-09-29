-- Prove2me | solution 1 for FoundationsML.Regression.rademacher_regression_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:09:40.315607+00:00
-- url     : https://prove2.me/submissions/5c7412ac-9354-4779-89d0-d2244174dae9

import Mathlib
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError
import Definitions.Def_FoundationsML_Regression_RademacherComplexity
import Definitions.Def_FoundationsML_Regression_EmpiricalRademacherComplexity

open MeasureTheory

namespace FoundationsML.Regression

/-- For samples of size `0`, the empirical Rademacher complexity vanishes. -/
theorem aux_rrb_erc_zero {Z : Type*} (G : Set (Z → ℝ)) (S : Fin 0 → Z) :
    EmpiricalRademacherComplexity G S = 0 := by
  unfold EmpiricalRademacherComplexity
  simp

/-- The counterexample set is empty. -/
theorem aux_rrb_set_empty :
    {S : Fin 0 → PUnit × ℝ | ∀ h ∈ ({fun _ => 0} : Set (PUnit → ℝ)),
        GeneralizationError (Measure.dirac ((PUnit.unit : PUnit), (0 : ℝ)))
            (fun _ _ => (1 : ℝ)) h ≤
          EmpiricalError S (fun _ _ => (1 : ℝ)) h +
            2 * (1 : ℝ) * RademacherComplexity
              (Measure.map Prod.fst (Measure.dirac ((PUnit.unit : PUnit), (0 : ℝ))))
              ({fun _ => 0} : Set (PUnit → ℝ)) 0 +
            (1 : ℝ) * Real.sqrt (Real.log (1 / (1 / 2 : ℝ)) / (2 * ((0 : ℕ) : ℝ)))} = ∅ := by
  ext S
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hS
  have h1 := hS (fun _ => 0) rfl
  have hR : RademacherComplexity
      (Measure.map Prod.fst (Measure.dirac ((PUnit.unit : PUnit), (0 : ℝ))))
      ({fun _ => 0} : Set (PUnit → ℝ)) 0 = 0 := by
    unfold RademacherComplexity
    simp [aux_rrb_erc_zero]
  rw [hR] at h1
  simp [GeneralizationError, EmpiricalError] at h1
  linarith

end FoundationsML.Regression

open FoundationsML.Regression
open MeasureTheory

theorem solution : ¬ (∀
    {X : Type} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M μ : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y')
    (hLb : ∀ y y', L y y' ≤ M) (hμ : 0 < μ)
    (hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ * |y1 - y2|)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Set (X → ℝ)) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            2 * μ * RademacherComplexity (Measure.map Prod.fst D) H m +
            M * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            2 * μ * EmpiricalRademacherComplexity H (fun i => (S i).1) +
            3 * M * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal) := by
  intro h
  have key := (h (X := PUnit) (Measure.dirac ((PUnit.unit : PUnit), (0 : ℝ)))
    (fun _ _ => (1 : ℝ)) 1 1 one_pos (fun _ _ => zero_le_one) (fun _ _ => le_rfl) one_pos
    (fun _ _ _ => by simp) measurable_const ({fun _ => 0} : Set (PUnit → ℝ))
    (fun _ hh => by rw [Set.mem_singleton_iff] at hh; subst hh; exact measurable_const)
    0 (1 / 2) (by norm_num)).1
  rw [aux_rrb_set_empty] at key
  simp at key
  norm_num at key
