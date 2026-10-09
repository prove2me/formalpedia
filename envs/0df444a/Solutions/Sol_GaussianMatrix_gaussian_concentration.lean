-- Prove2me | solution 1 for GaussianMatrix.gaussian_concentration
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T04:29:04.377201+00:00
-- url     : https://prove2.me/submissions/987c7360-fa18-4811-a3e6-ef3145f0b513

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_gaussian_concentration_vector

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix.Conc

/-- The Gaussian matrix law is the image of the flat standard Gaussian product measure on
`Fin p × Fin m → ℝ` under currying. -/
lemma gaussianMatrix_eq_map_curry (p m : ℕ) :
    gaussianMatrix p m =
      (Measure.pi fun _ : Fin p × Fin m => gaussianReal 0 1).map
        (MeasurableEquiv.curry (Fin p) (Fin m) ℝ) := by
  have := Measure.infinitePi_map_curry (fun (_ : Fin p) (_ : Fin m) => gaussianReal 0 1)
  simp only [Measure.infinitePi_eq_pi] at this
  rw [this]; rfl

/-- The Frobenius distance of two curried arrays is the Euclidean distance of the flat arrays. -/
lemma frobNorm_curry_sub {p m : ℕ} (x y : Fin p × Fin m → ℝ) :
    frobNorm (Matrix.of (MeasurableEquiv.curry (Fin p) (Fin m) ℝ x)
        - Matrix.of (MeasurableEquiv.curry (Fin p) (Fin m) ℝ y))
      = Real.sqrt (∑ ij, (x ij - y ij) ^ 2) := by
  unfold frobNorm frobSq
  congr 1
  rw [Fintype.sum_prod_type]
  rfl

end GaussianMatrix.Conc

open GaussianMatrix

theorem solution {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable h (gaussianMatrix p m) ∧
    (gaussianMatrix p m) {X | (∫ Y, h Y ∂(gaussianMatrix p m)) + L * t ≤ h X}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  open GaussianMatrix.Conc in
  set e := MeasurableEquiv.curry (Fin p) (Fin m) ℝ with he
  have hg : ∀ x y : Fin p × Fin m → ℝ,
      |(h ∘ e) x - (h ∘ e) y| ≤ L * Real.sqrt (∑ ij, (x ij - y ij) ^ 2) := by
    intro x y
    rw [← frobNorm_curry_sub]
    exact hLip _ _
  obtain ⟨hint, hmeas⟩ := gaussian_concentration_vector (h ∘ e) L hL hg t ht
  rw [gaussianMatrix_eq_map_curry]
  refine ⟨(integrable_map_equiv e h).mpr hint, ?_⟩
  rw [integral_map_equiv, e.map_apply]
  exact hmeas
