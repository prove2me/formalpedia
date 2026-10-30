-- Prove2me | solution 1 for DerivativeChainContinuation.sixth9_branch_at_infinity
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:55:26.941182+00:00
-- url     : https://prove2.me/submissions/835ce2f3-056d-4305-b509-06c171cb7fb7

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9InversePolynomial
import Definitions.Def_DerivativeChainContinuation_Sixth9PData
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_sixth9_first_positive_root
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open DerivativeChainContinuation in
theorem solution (W : ℂ → ℂ)
    (hW : ‖W 0-sixth9P 0‖ ≤ 1/100000000)
    (hroot : sixth9G 0 (W 0)=0) (hreal : (W 0).im=0) :
    2 < (W 0).re ∧ (W 0).re < 3 ∧
      4862-3003*(W 0).re+330*(W 0).re^2-2*(W 0).re^3=0 ∧
      ∀ r : ℝ,0 < r → 4862-3003*r+330*r^2-2*r^3=0 → (W 0).re ≤ r := by
  have hp : sixth9P 0=(sixth9PCoeffs 0:ℂ) := by simp [sixth9P,Fin.sum_univ_succ]
  have hpl : (2095/1000:ℝ) < (sixth9P 0).re := by rw [hp]; norm_num [sixth9PCoeffs]
  have hpu : (sixth9P 0).re < (2096/1000:ℝ) := by rw [hp]; norm_num [sixth9PCoeffs]
  have hd := (Complex.abs_re_le_norm (W 0-sixth9P 0)).trans hW
  rw [Complex.sub_re,abs_le] at hd
  have ha : 2 < (W 0).re ∧ (W 0).re < 3 := ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have hz : W 0=((W 0).re:ℂ) := by apply Complex.ext <;> simp [hreal]
  rw [hz] at hroot
  have he := congrArg Complex.re hroot
  norm_num [sixth9G,sixth9G0,sixth9G1,sixth9G2,← Complex.ofReal_pow,Complex.mul_re] at he
  exact ⟨ha.1,ha.2,he,sixth9_first_positive_root _ ha he⟩
