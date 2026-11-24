-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.exists_unit_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:18:24.064725+00:00
-- url     : https://prove2.me/submissions/f3065a01-9a84-4ec1-a82e-de19a76d1c46

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_dot_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {Q : Type} [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (X : Q → Q → ℂ) (j₀ : Q) :
    ∃ n : Q → ℂ, star n ⬝ᵥ n = 1 ∧ ∀ j, j ≠ j₀ → star n ⬝ᵥ X j = 0 := by
  have hd : ((cm (Function.update X j₀ 0))ᴴ).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero j₀ fun l => ?_
    simp [cm, Matrix.conjTranspose_apply]
  obtain ⟨n₀, hn₀, hM⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  set ν : ℝ := ∑ l, Complex.normSq (n₀ l) with hν
  have hνc : star n₀ ⬝ᵥ n₀ = (ν : ℂ) := by
    simp only [dotProduct, Pi.star_apply, hν, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have hνpos : 0 < ν := by
    have hne : ν ≠ 0 := by
      intro h
      apply hn₀
      have : star n₀ ⬝ᵥ n₀ = 0 := by rw [hνc, h]; simp
      exact dotProduct_star_self_eq_zero.1 this
    exact lt_of_le_of_ne (Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _) (Ne.symm hne)
  refine ⟨(((Real.sqrt ν)⁻¹ : ℝ) : ℂ) • n₀, ?_, fun j hj => ?_⟩
  · rw [star_smul, smul_dotProduct, dotProduct_smul, hνc]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    have := Real.sq_sqrt hνpos.le
    have h2 : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.2 hνpos).ne'
    field_simp
    linarith
  · have h1 : star (X j) ⬝ᵥ n₀ = 0 := by
      have := congrFun hM j
      have e : ((cm (Function.update X j₀ 0))ᴴ *ᵥ n₀) j = star (Function.update X j₀ 0 j) ⬝ᵥ n₀ := rfl
      rw [e, Function.update_of_ne hj] at this
      exact this
    rw [star_smul, smul_dotProduct, dot_conj, h1]; simp
end Formalism.FourierDecayAlt.P.HermitianFormFactor
