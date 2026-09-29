-- Prove2me | solution 1 for FoundationsML.Regression.pseudo_dimension_regression_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:27:40.327199+00:00
-- url     : https://prove2.me/submissions/e9b68c17-9d03-4fdf-8011-0faaec67bb16

import Mathlib
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError
import Definitions.Def_FoundationsML_Regression_LossComposedFamily
import Definitions.Def_FoundationsML_Regression_PseudoDim

open MeasureTheory

namespace FoundationsML.Regression

/-- The loss family of the constant loss `1` over `H = {0}` has pseudo-dimension `0`. -/
theorem aux_pdrb_pdim :
    PseudoDim (LossComposedFamily (fun _ _ => (1 : ℝ)) ({fun _ => 0} : Set (PUnit → ℝ))) 0 := by
  have hmem : (fun _ : PUnit × ℝ => (1 : ℝ)) ∈
      LossComposedFamily (fun _ _ => (1 : ℝ)) ({fun _ => 0} : Set (PUnit → ℝ)) :=
    ⟨fun _ => 0, rfl, rfl⟩
  refine ⟨⟨Fin.elim0, Fin.elim0, fun b => ⟨_, hmem, fun i => i.elim0⟩⟩, ?_⟩
  intro m ⟨z, t, ht⟩
  by_contra hm'
  have hm : 0 < m := by omega
  obtain ⟨g1, ⟨h1, hh1, rfl⟩, hg1⟩ := ht (fun _ => true)
  obtain ⟨g2, ⟨h2, hh2, rfl⟩, hg2⟩ := ht (fun _ => false)
  have a := (hg1 ⟨0, hm⟩).1 rfl
  have b := hg2 ⟨0, hm⟩
  simp only at a b
  exact absurd (b.2 a) (by simp)

/-- The counterexample set is empty. -/
theorem aux_pdrb_set_empty :
    {S : Fin 0 → PUnit × ℝ | ∀ h ∈ ({fun _ => 0} : Set (PUnit → ℝ)),
        GeneralizationError (Measure.dirac ((PUnit.unit : PUnit), (0 : ℝ)))
            (fun _ _ => (1 : ℝ)) h ≤
          EmpiricalError S (fun _ _ => (1 : ℝ)) h +
            (1 : ℝ) * Real.sqrt (2 * ((0 : ℕ) : ℝ) *
              Real.log (Real.exp 1 * ((0 : ℕ) : ℝ) / ((0 : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) +
            (1 : ℝ) * Real.sqrt (Real.log (1 / (1 / 2 : ℝ)) / (2 * ((0 : ℕ) : ℝ)))} = ∅ := by
  ext S
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hS
  have h1 := hS (fun _ => 0) rfl
  simp [GeneralizationError, EmpiricalError] at h1
  linarith

end FoundationsML.Regression

open FoundationsML.Regression
open MeasureTheory

theorem solution : ¬ (∀
    {X : Type} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Set (X → ℝ)) (hH_meas : ∀ h ∈ H, Measurable h)
    (d : ℕ) (hPdim : PseudoDim (LossComposedFamily L H) d)
    (m : ℕ) (hdm : d ≤ m) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            M * Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
            M * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro h
  have key := h (X := PUnit) (Measure.dirac ((PUnit.unit : PUnit), (0 : ℝ)))
    (fun _ _ => (1 : ℝ)) 1 one_pos (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
    measurable_const ({fun _ => 0} : Set (PUnit → ℝ))
    (fun _ hh => by rw [Set.mem_singleton_iff] at hh; subst hh; exact measurable_const)
    0 aux_pdrb_pdim 0 le_rfl (1 / 2) (by norm_num)
  rw [aux_pdrb_set_empty] at key
  simp at key
  norm_num at key
