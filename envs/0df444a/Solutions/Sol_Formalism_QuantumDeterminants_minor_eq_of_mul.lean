-- Prove2me | solution 1 for Formalism.QuantumDeterminants.minor_eq_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:41.23727+00:00
-- url     : https://prove2.me/submissions/16671a8d-5c0c-4a16-8155-72005b307a11

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Theorems.Thm_Formalism_QuantumDeterminants_sum_fin_castLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {m : ℕ} (L U X Y : Matrix (Fin m) (Fin m) ℂ)
    (hL0 : ∀ i j : Fin m, i < j → L i j = 0) (hL1 : ∀ i, L i i = 1)
    (hU0 : ∀ i j : Fin m, j < i → U i j = 0) (hU1 : ∀ i, U i i = 1)
    (h : L * X = Y * U) (l : ℕ) (hl : l ≤ m) :
    (X.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hord : ∀ i j : Fin l, i < j → Fin.castLE hl i < Fin.castLE hl j := fun i j h =>
    Fin.lt_def.2 (by simpa using Fin.lt_def.1 h)
  have h1 : (L * X).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      L.submatrix (Fin.castLE hl) (Fin.castLE hl) * X.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [submatrix_apply, mul_apply]
    rw [sum_fin_castLE hl (fun q => L (Fin.castLE hl i) q * X q (Fin.castLE hl j)) (fun q hq => by
      rw [hL0 _ _ (Fin.lt_def.2 (by simp; omega)), zero_mul])]
  have h2 : (Y * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [submatrix_apply, mul_apply]
    rw [sum_fin_castLE hl (fun q => Y (Fin.castLE hl i) q * U q (Fin.castLE hl j)) (fun q hq => by
      rw [hU0 _ _ (Fin.lt_def.2 (by simp; omega)), mul_zero])]
  have hdL : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_lowerTriangular (L.submatrix (Fin.castLE hl) (Fin.castLE hl)) (fun i j hij => hL0 _ _ (hord _ _ (OrderDual.toDual_lt_toDual.mp hij)))]
    simp [hL1]
  have hdU : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := U.submatrix (Fin.castLE hl) (Fin.castLE hl)) (fun i j hij => hU0 _ _ (hord _ _ hij))]
    simp [hU1]
  have h3 := congrArg Matrix.det
    (show (L * X).submatrix (Fin.castLE hl) (Fin.castLE hl) = (Y * U).submatrix (Fin.castLE hl) (Fin.castLE hl)
      by rw [h])
  rw [h1, h2, Matrix.det_mul, Matrix.det_mul, hdL, hdU, one_mul, mul_one] at h3
  exact h3
end Formalism.QuantumDeterminants
