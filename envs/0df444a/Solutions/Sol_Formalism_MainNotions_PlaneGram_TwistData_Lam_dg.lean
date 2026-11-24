-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Lam_dg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:50.890021+00:00
-- url     : https://prove2.me/submissions/91222373-7e65-4966-971e-62520fff1299

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_monomial_c
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_eq_lsup
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_apply

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
private theorem lam_sum_right (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (∑ i ∈ s, f i) = ∑ i ∈ s, D.abelian₂ p F (f i) := by
  simp only [lam_eq_sum_coeff_mul_ga_mul_fact, map_sum, MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm
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
theorem _root_.solution (F : MvPolynomial (D.OL × Fin D.r) K) (g : D.EM → K) (W : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (dg g W) = ∑ ζ ∈ W.support, g ζ * W.coeff ζ * D.abelian₂ p F (monomial ζ 1) := by
  rw [dg_eq_lsup, lsup_apply, lam_sum_right]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [lam_smul_right, Lam_monomial_c]
  ring
end Formalism.MainNotions.PlaneGram.TwistData
