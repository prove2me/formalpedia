-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cfc7bedf-f247-5a65-ab2f-9697c1ccc99c

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open MeasureTheory

theorem solution
    (K : Type) [Field K] [NumberField K] (pins : CarrierPins K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : ∀ x : AdeleRing (𝓞 K) K, ‖ψ x‖ = 1)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (χ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (a : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ⁻¹ (fun h : AdelicGL2 (𝓞 K) K => (starRingEnd ℂ) (φ h) * χ (Matrix.GeneralLinearGroup.det h)) a g =
      (starRingEnd ℂ) (whittakerCoefficient K pins ψ φ a g) * χ (Matrix.GeneralLinearGroup.det g) := by
  letI := pins.nS
  have hdet : ∀ x : AdeleRing (𝓞 K) K,
      Matrix.GeneralLinearGroup.det (unipotentGL2 x * g) = Matrix.GeneralLinearGroup.det g := by
    intro x
    rw [map_mul]
    have : Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 K) K) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of, Units.val_one]
      ring
    rw [this, one_mul]
  have hconj : ∀ y : AdeleRing (𝓞 K) K, (starRingEnd ℂ) (ψ (-y)) = ψ y := by
    intro y
    rw [← Complex.inv_eq_conj (hψ (-y)), AddChar.map_neg_eq_inv, inv_inv]
  show (∫ x, (starRingEnd ℂ) (φ (unipotentGL2 x * g)) * χ (Matrix.GeneralLinearGroup.det (unipotentGL2 x * g)) *
        ψ⁻¹ (-(algebraMap K (AdeleRing (𝓞 K) K) a * x)) ∂pins.ν) =
      (starRingEnd ℂ) (∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) a * x)) ∂pins.ν) *
        χ (Matrix.GeneralLinearGroup.det g)
  rw [← integral_conj, ← integral_mul_const]
  congr 1
  funext x
  rw [hdet x, AddChar.inv_apply, neg_neg, map_mul (starRingEnd ℂ), hconj]
  ring

end S_AutomorphicForm_whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul (solution)
