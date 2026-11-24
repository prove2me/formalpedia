-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.num_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:28:36.822743+00:00
-- url     : https://prove2.me/submissions/34338029-6ee4-42dd-9f4e-47b6d1e3c073

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
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
private theorem le_div_of_mul_le_of_pos {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  exact (le_div_iff₀ hc).2 h
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
theorem _root_.solution {T2 T1 R Dst D X L c b : ℝ} (hD : 0 < D) (hDs : 0 < Dst) (hDD : D ≤ L * Dst)
    (hX : 0 ≤ X) (hT2 : T2 ≤ R ^ 2 / Dst * X) (hb : 0 ≤ b * R) (hT1 : b * R ≤ T1)
    (hc : L * X ≤ c * b ^ 2) (hc0 : 0 ≤ c) : T2 ≤ c * T1 ^ 2 / D := by
  have ha : T2 * Dst ≤ R ^ 2 * X := by
    have h := mul_le_mul_of_nonneg_right hT2 hDs.le
    have e : R ^ 2 / Dst * X * Dst = R ^ 2 * X := by
      field_simp
    linarith
  have k1 : T2 * Dst * D ≤ R ^ 2 * X * D := mul_le_mul_of_nonneg_right ha hD.le
  have k2 : R ^ 2 * X * D ≤ R ^ 2 * X * (L * Dst) :=
    mul_le_mul_of_nonneg_left hDD (mul_nonneg (sq_nonneg R) hX)
  have k3 : R ^ 2 * (L * X) ≤ R ^ 2 * (c * b ^ 2) := mul_le_mul_of_nonneg_left hc (sq_nonneg R)
  have k3' := mul_le_mul_of_nonneg_right k3 hDs.le
  have k4 : (b * R) ^ 2 ≤ T1 ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hT1) (by linarith : (0:ℝ) ≤ T1 + b * R)]
  have k5 : c * (b * R) ^ 2 ≤ c * T1 ^ 2 := mul_le_mul_of_nonneg_left k4 hc0
  have k5' := mul_le_mul_of_nonneg_right k5 hDs.le
  have k6 : T2 * D * Dst ≤ c * T1 ^ 2 * Dst := by nlinarith
  have key : T2 * D ≤ c * T1 ^ 2 := le_of_mul_le_mul_right k6 hDs
  exact le_div_of_mul_le_of_pos hD key
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
