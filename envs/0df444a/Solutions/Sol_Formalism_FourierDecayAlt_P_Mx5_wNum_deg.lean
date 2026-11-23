-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.wNum_deg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:16.576521+00:00
-- url     : https://prove2.me/submissions/aecf1099-ba1a-499b-9ccf-6447f3f4f31f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_card_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (hk : 1 ≤ P.k) (π : Ty P) : (wNum P π).natDegree ≤ 2 * P.k ∧
    (wNum P π).coeff (2 * P.k) = -((P.T : ℂ) * P.T') := by
  have hm : (∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))).Monic :=
    monic_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _)
  have hd : (∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))).natDegree
      = 2 * P.k := by
    rw [natDegree_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _)]
    have : ∀ i ∈ Icc 1 P.k,
        ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2 := fun i _ => by
      rw [(monic_X_add_C _).natDegree_mul (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
    rw [sum_congr rfl this]
    simp [mul_comm]
  have he : ∀ (l : ℕ) (ρ : ℕ → ℂ), (∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (ρ j))).natDegree ≤ P.k - 1 := by
    intro l ρ
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]
    exact (card_le_card (erase_subset _ _)).trans (card_I P).le
  have ht : (∑ l ∈ Icc 1 (P.k - 1), C ((Nrm P l π : ℝ) : ℂ) *
      ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (rho P π j : ℂ))) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C ((rho P π j : ℂ) + 1)))).natDegree ≤
      (P.k - 1) + (P.k - 1) :=
    natDegree_sum_le_of_forall_le _ _ fun l _ => (natDegree_C_mul_le _ _).trans
      (natDegree_mul_le_of_le (he l _) (he l _))
  have hq : (qP P).natDegree ≤ 2 * P.k := (natDegree_C_mul_le _ _).trans hd.le
  constructor
  · exact natDegree_add_le_of_degree_le hq (ht.trans (by omega))
  · unfold wNum
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ht (by omega)), add_zero, qP,
      coeff_C_mul, ← hd, hm.coeff_natDegree, mul_one]
end Formalism.FourierDecayAlt.P.Mx5
