-- Prove2me | solution 1 for Formalism.DivisionValues.one_le_det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:22.486621+00:00
-- url     : https://prove2.me/submissions/ee40ae65-ad14-47b3-8308-8e7f3b38383c

import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DeterminantCauchySchwarz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution {m : Type*} [Fintype m] [DecidableEq m] {Z : Matrix m m ℂ}
    (hZ : Z.PosSemidef) : (1 : ℂ) ≤ (1 + Z).det := by
  have hspec := hZ.1.spectral_theorem
  have hUU : (hZ.1.eigenvectorUnitary : Matrix m m ℂ) * star (hZ.1.eigenvectorUnitary : Matrix m m ℂ) = 1 := by
    simp
  have hdet : ∀ x : Matrix m m ℂ, ((hZ.1.eigenvectorUnitary : Matrix m m ℂ) * x *
      star (hZ.1.eigenvectorUnitary : Matrix m m ℂ)).det = x.det := by
    intro x
    rw [det_mul, det_mul, mul_comm (det (hZ.1.eigenvectorUnitary : Matrix m m ℂ)), mul_assoc, ← det_mul, hUU,
      det_one, mul_one]
  have key : 1 + Z = (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) hZ.1.eigenvectorUnitary)
      (1 + diagonal (RCLike.ofReal ∘ hZ.1.eigenvalues)) := by
    rw [map_add, map_one, ← hspec]
  rw [key, Unitary.conjStarAlgAut_apply, hdet, ← diagonal_one, diagonal_add, det_diagonal]
  have hev := hZ.eigenvalues_nonneg
  have hprod : ∏ i, ((1 : ℂ) + (RCLike.ofReal ∘ hZ.1.eigenvalues) i) =
      ((∏ i, (1 + hZ.1.eigenvalues i) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, ← Complex.ofReal_one, Complex.real_le_real]
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => by linarith [hev i])
end Formalism.DivisionValues
