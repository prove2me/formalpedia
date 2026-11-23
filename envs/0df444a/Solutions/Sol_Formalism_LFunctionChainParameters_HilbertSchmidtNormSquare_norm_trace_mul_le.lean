-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.norm_trace_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:58.155358+00:00
-- url     : https://prove2.me/submissions/cc9d30fb-983c-4b08-ba89-8411e0379272

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_nonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexOrder
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
section HS
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
end HS
section Fam
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
end Fam
section CS
variable {m n : Type} [Fintype m] [Fintype n]
private theorem le_sqrt_of_sq_le' {x y : ℝ} (h : x ^ 2 ≤ y) : x ≤ Real.sqrt y := by
  refine (le_abs_self x).trans ?_
  exact Real.abs_le_sqrt h
private theorem sum_norm_mul_le_hsNorm_mul (A B : Matrix m n ℂ) :
    ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ ≤ hsNorm A * hsNorm B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (m × n))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
  simp only [Fintype.sum_prod_type] at h
  unfold hsNorm
  rw [← Real.sqrt_mul (hsSq_nonneg A)]
  exact le_sqrt_of_sq_le' h
end CS
section Tri
variable {m n : Type} [Fintype m] [Fintype n]
end Tri
section Cor
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
end Cor
section Compress
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq k]
end Compress
section Ram
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
end Ram
section RamTr
end RamTr
section RamMain
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
end RamMain
section Num
end Num
section Final
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
end Final
end
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
end

set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {m n : Type} [Fintype m] [Fintype n]
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (X : Matrix m n ℂ) (Y : Matrix n m ℂ) :
    ‖(X * Y).trace‖ ≤ hsNorm X * hsNorm Y := by
  have h1 : ‖(X * Y).trace‖ ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Yᵀ i j‖ := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  have h2 : hsNorm Yᵀ = hsNorm Y := by
    unfold hsNorm hsSq
    simp only [Matrix.transpose_apply]
    rw [Finset.sum_comm]
  rw [← h2]
  exact h1.trans (sum_norm_mul_le_hsNorm_mul X Yᵀ)
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
