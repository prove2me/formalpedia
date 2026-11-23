-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.gramC_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:23.069052+00:00
-- url     : https://prove2.me/submissions/56c1c57e-1423-449b-af1e-16f6cc47ce22

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Theorems.Thm_Formalism_L2_LamCM_A2_gramC_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    (ReciprocityTheory.MultiplicativeHeights.gramC H σ b).det = (Complex.normSq (σ (Matrix.of b).det) : ℂ) * H.det := by
  rw [gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose,
    RingHom.map_det σ (Matrix.of b), Complex.normSq_eq_conj_mul_self]
  simp only [RingHom.mapMatrix_apply, Complex.star_def]
  ring
end Formalism.L2.LamCM.A2
