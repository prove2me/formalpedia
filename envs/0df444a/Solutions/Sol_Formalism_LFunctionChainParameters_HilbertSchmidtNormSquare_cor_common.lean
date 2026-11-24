-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.cor_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:43:05.281799+00:00
-- url     : https://prove2.me/submissions/f861e1a3-499c-4749-a71d-4bbb1bcc7042

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trQ_lower
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trQsq_upper
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
private theorem mul_le_of_div_le_of_pos {a b c : ℝ} (hc : 0 < c) (h : a / c ≤ b) : a ≤ b * c := by
  exact (div_le_iff₀ hc).1 h
end Final
end
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
end

set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {Dstar sg η0 η1 e0 : ℝ} (hD : 0 < Dstar) (hs0 : 0 < sg) (hs : sg ≤ 1 / 4)
    (hR : Dstar / sg ≤ Rs d) (hη0 : -1 ≤ η0) (he : 0 ≤ e0) (ha' : Real.sqrt e0 ≤ sg / 2)
    (hS : InputS B ga Dstar η0 η1 e0) :
    0 < (D : ℝ) ∧ 0 ≤ 1 + η1 ∧ 0 < Rs d ∧
    (Qm B ga * Qm B ga).trace.re
      ≤ Rs d ^ 2 / Dstar * ((1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg) ∧
    (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re := by
  obtain ⟨hP, hK, hDD⟩ := hS
  have hT : 0 < Rs d := lt_of_lt_of_le (div_pos hD hs0) hR
  have hae : Real.sqrt e0 ≤ 1 / 8 := by linarith
  have hF1 := trQ_lower B ga hga he hK
  have hDpos : 0 < (D : ℝ) := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · exfalso
      subst h0
      have h2 : (Qm B ga).trace = 0 := by simp [Matrix.trace]
      rw [h2, Complex.zero_re] at hF1
      have := mul_pos (by linarith : (0:ℝ) < 1 - Real.sqrt e0) hT
      linarith
    · exact_mod_cast h0
  have hL : 0 ≤ 1 + η1 := by
    by_contra h
    push_neg at h
    have h1 := mul_neg_of_neg_of_pos h hD
    linarith
  have hF2 := trQsq_upper B ga hga hD hη0 he hP hK
  have hDle : Dstar ≤ Rs d * sg := mul_le_of_div_le_of_pos hs0 hR
  have hTT : Rs d ≤ Rs d ^ 2 / Dstar * sg := by
    rw [div_mul_eq_mul_div]
    apply le_div_of_mul_le_of_pos hD
    nlinarith [mul_le_mul_of_nonneg_left hDle hT.le]
  have he2 : Rs d ^ 2 / Dstar * ((1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg)
      = (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * (Rs d ^ 2 / Dstar * sg) := by
    ring
  have hm := mul_le_mul_of_nonneg_left hTT (sq_nonneg (1 + Real.sqrt e0))
  refine ⟨hDpos, hL, hT, ?_, hF1⟩
  rw [he2]
  linarith
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
