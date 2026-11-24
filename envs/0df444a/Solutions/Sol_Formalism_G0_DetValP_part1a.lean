-- Prove2me | solution 1 for Formalism.G0.DetValP.part1a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:37.728903+00:00
-- url     : https://prove2.me/submissions/ff8a054d-f6f6-4b70-b87c-7c05a72b7c96

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Theorems.Thm_Formalism_G0_DetValP_substS_det
import Theorems.Thm_Formalism_G0_DetValP_substS_X
import Theorems.Thm_Formalism_G0_DetValP_prod_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetValP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetValP
theorem _root_.solution {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hv : ∀ l, vec (A l) = true) (hS : ∀ l, A l ∈ S)
    (g : GL (Fin r) L) :
    MvPolynomial.C Polynomial.X ∣ substS (K := K) vec S g (detLetters A) := by
  have h1 : substS (K := K) vec S g (detLetters A) =
      Matrix.det ((Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) *
        ((msMat g).map MvPolynomial.C).transpose) := by
    have := substS_det (K := K) vec S g A (RingHom.id _)
    simp only [RingHom.id_apply] at this
    rw [this]
    congr 1
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, substS_X]
    simp only [hS l, hv l, if_true, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hC := RingHom.map_det (MvPolynomial.C : Polynomial L →+* MvPolynomial (ι × Fin r) (Polynomial L)) (msMat g)
  rw [RingHom.mapMatrix_apply] at hC
  rw [h1, Matrix.det_mul, Matrix.det_transpose, ← hC]
  apply dvd_mul_of_dvd_right
  apply map_dvd
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_last hr]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
end Formalism.G0.DetValP
