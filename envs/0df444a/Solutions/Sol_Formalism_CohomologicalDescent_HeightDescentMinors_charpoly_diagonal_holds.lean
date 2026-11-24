-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.charpoly_diagonal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:40:18.349211+00:00
-- url     : https://prove2.me/submissions/38a3426d-4824-408f-986c-43d46a0ebfcc

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : CharpolyDiag := by
  intro O L _ _ ι n Θ Γ lam r G hι hlam hΓ hG
  have ha : ι lam ≠ 0 := fun h => hlam (hι (by simpa using h))
  have h1 : Γ.map ι = 1 + ι lam • Θ.map ι := by
    rw [hΓ]; ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, hij]
  have h2 : Matrix.diagonal (fun j => ι (1 + lam * r j)) =
      1 + ι lam • Matrix.diagonal (fun j => ι (r j)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h1, h2, add_mul, mul_add, one_mul, mul_one, add_right_inj, Matrix.smul_mul,
    Matrix.mul_smul] at hG
  have h3 : Θ.map ι * (G : Matrix (Fin n) (Fin n) L) =
      (G : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun j => ι (r j)) :=
    smul_right_injective _ ha hG
  have h4 : Θ.map ι = (G : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun j => ι (r j)) *
      ((G⁻¹ : (Matrix (Fin n) (Fin n) L)ˣ) : Matrix (Fin n) (Fin n) L) := by
    rw [← h3, mul_assoc, Units.mul_inv, mul_one]
  apply Polynomial.map_injective ι hι
  rw [← Matrix.charpoly_map, h4, Matrix.coe_units_inv, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal,
    Polynomial.map_prod]
  simp
end Formalism.CohomologicalDescent.HeightDescentMinors
