-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:41.841368+00:00
-- url     : https://prove2.me/submissions/5c639527-8840-4a85-945e-56d5fb70d261

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsNorm_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsNorm_sq
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
theorem _root_.solution (A B : Matrix m n ℂ) : hsSq (A + B) ≤ (hsNorm A + hsNorm B) ^ 2 := by
  have h1 : hsSq (A + B)
      ≤ ∑ i, ∑ j, (‖A i j‖ ^ 2 + ‖B i j‖ ^ 2 + 2 * (‖A i j‖ * ‖B i j‖)) := by
    unfold hsSq
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [Matrix.add_apply]
    nlinarith [norm_add_le (A i j) (B i j), norm_nonneg (A i j + B i j), norm_nonneg (A i j),
      norm_nonneg (B i j)]
  have e : ∑ i, ∑ j, (‖A i j‖ ^ 2 + ‖B i j‖ ^ 2 + 2 * (‖A i j‖ * ‖B i j‖))
      = hsSq A + hsSq B + 2 * ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ := by
    unfold hsSq
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have h2 := sum_norm_mul_le_hsNorm_mul A B
  have hA := hsNorm_sq A
  have hB := hsNorm_sq B
  nlinarith [hsNorm_nonneg A, hsNorm_nonneg B]
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
