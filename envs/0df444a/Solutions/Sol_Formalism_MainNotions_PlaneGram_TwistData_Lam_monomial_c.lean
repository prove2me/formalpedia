-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Lam_monomial_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:33.142854+00:00
-- url     : https://prove2.me/submissions/8d0432d1-1ca5-4efa-bbe4-f8d51d45cfbd

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
namespace TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
private theorem lam_eq_sum_coeff_mul_ga_mul_fact (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K)
    (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F Z = ∑ α ∈ F.support, F.coeff α * (D.ga α * (D.ph p Z).coeff α) * (fact α : K) := by
  unfold abelian₂ fock
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 2
  unfold gaAct
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [show (D.ph p Z).coeff α = 0 by simpa using h, mul_zero]
private theorem lam_smul_right (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (c : K)
    (Z : MvPolynomial (D.ML × Fin D.r) K) : D.abelian₂ p F (c • Z) = c * D.abelian₂ p F Z := by
  simp only [lam_eq_sum_coeff_mul_ga_mul_fact, map_smul, MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring
end TwistData
end Formalism.MainNotions.PlaneGram
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) (c : K) :
    D.abelian₂ p F (monomial ζ c) = c * D.abelian₂ p F (monomial ζ 1) := by
  rw [show (monomial ζ c : MvPolynomial (D.ML × Fin D.r) K) = c • monomial ζ 1 by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], lam_smul_right]
end Formalism.MainNotions.PlaneGram.TwistData
