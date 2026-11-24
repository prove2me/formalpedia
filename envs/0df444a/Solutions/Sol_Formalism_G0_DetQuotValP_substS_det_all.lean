-- Prove2me | solution 1 for Formalism.G0.DetQuotValP.substS_det_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:22.785585+00:00
-- url     : https://prove2.me/submissions/5f9ef729-4bdd-473e-81c4-38966357d1f4

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal
import Theorems.Thm_Formalism_G0_DetQuotValP_det_msMat
import Theorems.Thm_Formalism_G0_DetValP_substS_X
import Theorems.Thm_Formalism_G0_DetValP_substS_det


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
open Formalism Formalism.G0 Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetQuotValP
theorem _root_.solution {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hv : ∀ l, vec (A l) = true) (hS : ∀ l, A l ∈ S)
    (g : GL (Fin r) L) :
    substS (K := K) vec S g (detLetters A) =
      MvPolynomial.C Polynomial.X * Matrix.det (Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) := by
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
  rw [h1, Matrix.det_mul, Matrix.det_transpose, ← hC, det_msMat hr, mul_comm]
end Formalism.G0.DetQuotValP
