-- Prove2me | solution 1 for FoundationsML.Regression.finite_hypothesis_regression_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:29:47.142889+00:00
-- url     : https://prove2.me/submissions/44451caa-0c96-40bb-adce-5edd53ebc3ca

import Mathlib
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError

open MeasureTheory

namespace FoundationsML.Regression

/-- With zero samples and the constant loss `1`, the target event is empty. -/
theorem aux_fhrb_set_empty :
    {S : Fin 0 → Unit × ℝ | ∀ h ∈ ({fun _ => 0} : Finset (Unit → ℝ)),
        GeneralizationError (Measure.dirac ((), (0 : ℝ))) (fun _ _ => (1 : ℝ)) h ≤
          EmpiricalError S (fun _ _ => (1 : ℝ)) h +
            1 * Real.sqrt ((Real.log ({fun _ => 0} : Finset (Unit → ℝ)).card
              + Real.log (1 / (1 / 2 : ℝ))) / (2 * ((0 : ℕ) : ℝ)))} = ∅ := by
  ext S
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hS
  have := hS (fun _ => 0) (Finset.mem_singleton_self _)
  simp [GeneralizationError, EmpiricalError] at this
  linarith

end FoundationsML.Regression

open FoundationsML.Regression

theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Finset (X → ℝ)) (hHne : H.Nonempty) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            M * Real.sqrt ((Real.log H.card + Real.log (1 / δ)) / (2 * m))}).toReal) := by
  intro hAll
  have key := hAll (X := Unit) (Measure.dirac ((), (0 : ℝ))) (fun _ _ => (1 : ℝ)) 1 one_pos
    (fun _ _ => zero_le_one) (fun _ _ => le_rfl) measurable_const
    {fun _ => 0} (Finset.singleton_nonempty _)
    (fun h hh => by rw [Finset.mem_singleton.mp hh]; exact measurable_const)
    0 (1 / 2) (by norm_num)
  rw [aux_fhrb_set_empty] at key
  simp at key
  norm_num at key
