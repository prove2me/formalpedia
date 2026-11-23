-- Prove2me | solution 1 for Formalism.G0.DetDividesP.msMat_mul_nMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:45.31733+00:00
-- url     : https://prove2.me/submissions/73a9d4c7-189f-448e-9277-e2d3986de868

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

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
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {L : Type} [Field L] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (g : GL (Fin r) L) : msMat g * nMat g = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
  unfold msMat nMat
  have hgi : ((g⁻¹ : GL (Fin r) L).1.map C) * (g.1.map C) = 1 := by
    rw [← Matrix.map_mul]; simp
  have hgg : (g.1.map C) * ((g⁻¹ : GL (Fin r) L).1.map C) = 1 := by
    rw [← Matrix.map_mul]; simp
  have hdd : Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1; funext a; split_ifs <;> simp
  calc (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
        ((g⁻¹ : GL (Fin r) L).1.map C) * ((g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C))
      = (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
        (((g⁻¹ : GL (Fin r) L).1.map C) * (g.1.map C)) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C) := by simp only [Matrix.mul_assoc]
    _ = (g.1.map C) * ((X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X])) * ((g⁻¹ : GL (Fin r) L).1.map C) := by
        rw [hgi, Matrix.mul_one, Matrix.mul_assoc (g.1.map C), hdd]
    _ = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hgg]
end Formalism.G0.DetDividesP
