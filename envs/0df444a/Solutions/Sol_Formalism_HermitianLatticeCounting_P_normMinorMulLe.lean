-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.normMinorMulLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:38.67747+00:00
-- url     : https://prove2.me/submissions/43e97371-7585-4f8d-b662-92e04c78cb22

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_det_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MinorBound := by
  intro N A w B ρ P hρ hA hB hw t I J
  have hP : 0 ≤ P := (norm_nonneg _).trans (hw 0 Fin.elim0 Fin.elim0)
  have e : (A * w * B).submatrix I J = (A.submatrix I id) * ((w * B).submatrix id J) := by
    rw [Matrix.mul_assoc]; ext i j; simp [Matrix.mul_apply]
  rw [e]
  have h2 : ∀ f : Fin t → Fin N, ‖(((w * B).submatrix id J).submatrix f id).det‖ ≤
      (N.factorial : ℝ) * ρ ^ N * P := by
    intro f
    have e2 : ((w * B).submatrix id J).submatrix f id =
        ((B.submatrix id J)ᵀ * (w.submatrix f id)ᵀ)ᵀ := by
      rw [← Matrix.transpose_mul]; ext i j; simp [Matrix.mul_apply, mul_comm]
    rw [e2, Matrix.det_transpose]
    apply norm_det_mul_le _ _ ρ P hρ hP (fun i k => hB _ _)
    intro g
    have : ((w.submatrix f id)ᵀ).submatrix g id = (w.submatrix f g)ᵀ := by ext i j; simp
    rw [this, Matrix.det_transpose]; exact hw t f g
  have h1 := norm_det_mul_le (A.submatrix I id) ((w * B).submatrix id J) ρ _ hρ (by positivity)
    (fun i k => hA _ _) h2
  refine h1.trans ?_
  have h4 : (1:ℝ) ≤ 4 ^ N := one_le_pow₀ (by norm_num)
  calc (N.factorial : ℝ) * ρ ^ N * ((N.factorial : ℝ) * ρ ^ N * P)
      = 1 * ((N.factorial : ℝ) ^ 2 * ρ ^ (2 * N) * P) := by ring
    _ ≤ 4 ^ N * ((N.factorial : ℝ) ^ 2 * ρ ^ (2 * N) * P) := by gcongr
    _ = _ := by ring
end Formalism.HermitianLatticeCounting.P
