-- Prove2me | solution 1 for Formalism.GM.smith_form_p_adic_integers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:27:45.05113+00:00
-- url     : https://prove2.me/submissions/e001f08b-4930-4f55-bbc6-e1dec1f2600c

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_SmithDeterminants_TruncationChainBoundNonnegExponents
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Theorems.Thm_Formalism_A_smithExists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Matrix
namespace Formalism.GM
theorem _root_.solution : SmithZp := by
  intro p _ n M
  classical
  let y : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p]) := Matrix.toLin' M
  obtain ⟨S⟩ := Formalism.A.smithExists ℤ_[p] (Fin n → ℤ_[p]) y
  have hfr : Module.finrank ℤ_[p] (Fin n → ℤ_[p]) = n := Module.finrank_fin_fun ℤ_[p]
  let e : Fin (Module.finrank ℤ_[p] (Fin n → ℤ_[p])) ≃ Fin n := finCongr hfr
  let b := S.b.reindex e
  let b' := S.b'.reindex e
  let a : Fin n → ℤ_[p] := S.a ∘ e.symm
  have hy : ∀ j, M.mulVec (b j) = a j • b' j := by
    intro j
    have := S.hy (e.symm j)
    simpa [b, b', a, y, Matrix.toLin'_apply] using this
  let std := Pi.basisFun ℤ_[p] (Fin n)
  let Q := std.toMatrix b
  let P := std.toMatrix b'
  let V := b.toMatrix std
  have hQV : Q * V = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std b
  have hPW : P * (b'.toMatrix std) = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std b'
  have hMQ : M * Q = P * Matrix.diagonal a := by
    ext i j
    have h1 := congrFun (hy j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Q, P, std, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h1]; ring
  refine ⟨P, V, a, Matrix.isUnit_det_of_right_inverse hPW, Matrix.isUnit_det_of_left_inverse hQV, ?_⟩
  calc M = M * (Q * V) := by rw [hQV, Matrix.mul_one]
    _ = (M * Q) * V := by rw [Matrix.mul_assoc]
    _ = P * Matrix.diagonal a * V := by rw [hMQ]
end Formalism.GM
