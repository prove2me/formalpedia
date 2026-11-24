-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.ram_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:42:47.682953+00:00
-- url     : https://prove2.me/submissions/b5507d8b-1aa8-4d7b-9c18-75eba47d7bef

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trace_conjTranspose_mul_self
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_norm_trace_mul_le
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsNorm_le_of_sq
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_proj_herm
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_proj_idem
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trace_proj
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
theorem _root_.solution (n k : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ)
    (hV : Vᴴ * V = 1) {e0 : ℝ} (he : 0 ≤ e0) (hK : hsSq (K - 1) ≤ e0 * n) :
    0 ≤ (n : ℝ) - k ∧
    K.trace.re - (Vᴴ * K * V).trace.re
      ≤ ((n : ℝ) - k) + Real.sqrt ((n : ℝ) - k) * (Real.sqrt e0 * Real.sqrt n) := by
  have hP1 : (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    rw [proj_herm V, proj_idem V hV]
  have hnk : hsSq (1 - V * Vᴴ) = (n : ℝ) - k := by
    have h := trace_conjTranspose_mul_self (1 - V * Vᴴ)
    rw [hP1, trace_proj n k V hV] at h
    exact (Complex.ofReal_injective h).symm
  have hnk0 : 0 ≤ (n : ℝ) - k := by
    rw [← hnk]
    exact hsSq_nonneg _
  refine ⟨hnk0, ?_⟩
  have hc : (Vᴴ * K * V).trace = (K * (V * Vᴴ)).trace := by
    rw [Matrix.trace_mul_comm (Vᴴ * K) V, Matrix.trace_mul_comm K (V * Vᴴ), Matrix.mul_assoc]
  have htr : K.trace - (Vᴴ * K * V).trace
      = (1 - V * Vᴴ).trace + ((K - 1) * (1 - V * Vᴴ)).trace := by
    rw [hc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub]
    ring
  have hcs := norm_trace_mul_le (K - 1) (1 - V * Vᴴ)
  have hN1 : hsNorm (1 - V * Vᴴ) = Real.sqrt ((n : ℝ) - k) := by
    unfold hsNorm
    rw [hnk]
  rw [hN1] at hcs
  have hNK := hsNorm_le_of_sq _ he hK
  have hre : (K.trace - (Vᴴ * K * V).trace).re
      = ((n : ℝ) - k) + ((K - 1) * (1 - V * Vᴴ)).trace.re := by
    rw [htr, Complex.add_re, trace_proj n k V hV, Complex.ofReal_re]
  rw [Complex.sub_re] at hre
  have habs := re_le_norm' (((K - 1) * (1 - V * Vᴴ)).trace)
  have hs := Real.sqrt_nonneg ((n : ℝ) - k)
  have hm := mul_le_mul_of_nonneg_left hNK hs
  linarith
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
