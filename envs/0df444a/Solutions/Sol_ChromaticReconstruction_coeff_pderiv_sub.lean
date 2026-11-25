-- Prove2me | solution 1 for ChromaticReconstruction.coeff_pderiv_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:47:49.12889+00:00
-- url     : https://prove2.me/submissions/6b9d3fe0-e0f1-4b3a-9068-fa2b935a1e87

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (f : MvPolynomial ℕ ℚ) (r : ℕ) (d : ℕ →₀ ℕ) (hd : 1 ≤ d r) :
    coeff (d - Finsupp.single r 1) (pderiv r f) = d r * coeff d f := by
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hs : s r = 0
    · have : s ≠ d := fun h => by rw [h] at hs; omega
      simp [hs, this]
    · by_cases hsd : s = d
      · subst hsd; simp [mul_comm]
      · rw [if_neg, if_neg hsd, mul_zero]
        intro h
        apply hsd
        ext x
        have := DFunLike.congr_fun h x
        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply] at this
        split_ifs at this with hx
        · subst hx; omega
        · omega
  | add p q hp hq => simp [hp, hq, mul_add]
end ChromaticReconstruction
