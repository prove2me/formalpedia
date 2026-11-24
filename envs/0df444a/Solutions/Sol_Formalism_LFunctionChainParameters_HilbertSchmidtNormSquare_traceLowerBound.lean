-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.traceLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:28:37.375431+00:00
-- url     : https://prove2.me/submissions/6b85fc3f-1e7c-4986-8a67-dac9dba6fb3f

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_norm_trace_mul_le
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_one
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
end CS
private theorem re_le_norm' (z : ℂ) : z.re ≤ ‖z‖ := by
  exact Complex.re_le_norm z
private theorem neg_re_le_norm' (z : ℂ) : -z.re ≤ ‖z‖ := by
  have h := re_le_norm' (-z)
  rwa [Complex.neg_re, norm_neg] at h
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
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution : TraceLower := by
  intro n K
  have h1 : K.trace = (n : ℂ) + ((1 : Matrix (Fin n) (Fin n) ℂ) * (K - 1)).trace := by
    rw [one_mul, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin]
    ring
  have h2 := norm_trace_mul_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
  have h3 : hsNorm (1 : Matrix (Fin n) (Fin n) ℂ) = Real.sqrt n := by
    unfold hsNorm
    rw [hsSq_one]
  rw [h3] at h2
  have h4 := neg_re_le_norm' (((1 : Matrix (Fin n) (Fin n) ℂ) * (K - 1)).trace)
  have h5 : ((n : ℂ)).re = (n : ℝ) := by simp
  rw [h1, Complex.add_re, h5]
  linarith
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
