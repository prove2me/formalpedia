-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_radial_characteristic_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T17:31:15.807593+00:00
-- url     : https://prove2.me/submissions/0ae6a29b-3941-43c7-82b9-f3d95e7eff69

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf

open BirkhoffGlobalSection

private theorem coordinateExpansion (L : Phase →L[ℝ] ℝ) (v : Phase) :
    L v = v 0 * L (coordinateVector 0) + v 1 * L (coordinateVector 1) +
      v 2 * L (coordinateVector 2) + v 3 * L (coordinateVector 3) := by
  have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  calc
    L v = L (v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3) := congrArg L hv
    _ = _ := by simp

/-- Algebraic part of the Hamiltonian/Reeb correspondence. On a regular energy
level the derivative kernel is its tangent space. Here the conclusions are
stated directly in that kernel; no manifold contact or complete-flow theorem
is assumed or asserted. Source: Hryniewicz v5, p. 1, equations (2), and p. 2,
the characteristic-line description, in the workspace sign convention. -/
theorem solution (F : Phase → ℝ) (y : Phase)
    (hpos : 0 < phaseRadialContact y (hamiltonianVectorField F y)) :
    let X := hamiltonianVectorField F y
    let R := (phaseRadialContact y X)⁻¹ • X
    phaseRadialContact y R = 1 ∧
      fderiv ℝ F y R = 0 ∧
      (∀ v : Phase, fderiv ℝ F y v = 0 → phaseSymplecticForm R v = 0) ∧
      phaseRadialContact y X = fderiv ℝ F y y / 2 := by
  have hcoeff (v : Phase) : fderiv ℝ F y v =
    v 0 * partialDerivative F y 0 + v 1 * partialDerivative F y 1 +
    v 2 * partialDerivative F y 2 + v 3 * partialDerivative F y 3 :=
    coordinateExpansion (fderiv ℝ F y) v
  have hsymp (v : Phase) :
      phaseSymplecticForm (hamiltonianVectorField F y) v = fderiv ℝ F y v := by
    rw [hcoeff v]
    simp [phaseSymplecticForm, hamiltonianVectorField]
    ring
  have hpair : phaseRadialContact y (hamiltonianVectorField F y) =
      fderiv ℝ F y y / 2 := by
    rw [hcoeff y]
    simp [phaseRadialContact, phaseSymplecticForm, hamiltonianVectorField]
    ring
  have hzero : fderiv ℝ F y (hamiltonianVectorField F y) = 0 := by
    rw [← hsymp]
    simp [phaseSymplecticForm]
    ring
  dsimp only
  refine ⟨?_, ?_, ?_, hpair⟩
  · have hscale (a : ℝ) :
        phaseRadialContact y (a • hamiltonianVectorField F y) =
          a * phaseRadialContact y (hamiltonianVectorField F y) := by
      simp [phaseRadialContact, phaseSymplecticForm]
      ring
    rw [hscale]
    exact inv_mul_cancel₀ (ne_of_gt hpos)
  · simp [hzero]
  · intro v hv
    have hscale (a : ℝ) :
        phaseSymplecticForm (a • hamiltonianVectorField F y) v =
          a * phaseSymplecticForm (hamiltonianVectorField F y) v := by
      simp [phaseSymplecticForm]
      ring
    rw [hscale, hsymp, hv, mul_zero]
