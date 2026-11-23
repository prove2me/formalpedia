-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.pf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:28.144643+00:00
-- url     : https://prove2.me/submissions/71668d10-f491-49dd-82a9-8696209f9daf

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pf_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_q_polynomial_monic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_natDegree_q1_polynomial
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_qC_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_rhoC_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_moduleH1Alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_residue_quadratic_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_double_root_of_adjacent_rho
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_modE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) (u : ℂ) (h0 : xC P π (u - 1) ≠ 0) (h1 : xC P π u ≠ 0)
    (h2 : xC P π (u + 1) ≠ 0) :
    qC P (u - 1) * ((xC P π (u - 1))⁻¹ * (xC P π u)⁻¹) - qC P u * ((xC P π u)⁻¹ * (xC P π (u + 1))⁻¹) =
      (2 * (aC P π : ℂ) + 2 * u) * (P.TT : ℂ) + ∑ l ∈ Icc 1 (P.k - 1),
        ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
          (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) := by
  obtain ⟨r, hr⟩ := pf_abs (Icc 1 (P.k - 1)) (fun i => (rho P π i : ℂ)) (rhoC_inj P hP π)
    (-((P.T : ℂ) * P.T')) (q1P P) (fun l => (Nrm P l π : ℂ)) (fun l => (NrmDown P l π : ℂ))
    (moduleH1Alt P hP π) (residue_quadratic_identity P hP π) (double_root_of_adjacent_rho P hP π) (q_polynomial_monic P)
    (by rw [natDegree_q1_polynomial, Nat.card_Icc]; have := hP.k_pos; omega) (2 * (aC P π : ℂ) + 1) (modE P hP π)
  have f0 : ∀ i ∈ Icc 1 (P.k - 1), u - 1 + (rho P π i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.1 h0
  have f1 : ∀ i ∈ Icc 1 (P.k - 1), u + (rho P π i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.1 h1
  have f2 : ∀ i ∈ Icc 1 (P.k - 1), u + 1 + (rho P π i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.1 h2
  have E0 := hr (u - 1) f0 (fun i hi h => f1 i hi (by linear_combination h))
  have E1 := hr u f1 (fun i hi h => f2 i hi (by linear_combination h))
  have p0 : ∏ i ∈ Icc 1 (P.k - 1), (u - 1 + ((rho P π i : ℂ) + 1)) = xC P π u :=
    Finset.prod_congr rfl (fun i _ => by ring)
  have p1 : ∏ i ∈ Icc 1 (P.k - 1), (u + ((rho P π i : ℂ) + 1)) = xC P π (u + 1) :=
    Finset.prod_congr rfl (fun i _ => by ring)
  have x0 : ∏ i ∈ Icc 1 (P.k - 1), (u - 1 + (rho P π i : ℂ)) = xC P π (u - 1) := rfl
  have x1 : ∏ i ∈ Icc 1 (P.k - 1), (u + (rho P π i : ℂ)) = xC P π u := rfl
  rw [p0, x0, ← qC_eq] at E0
  rw [p1, x1, ← qC_eq] at E1
  rw [E0, E1]
  have T : ∀ l ∈ Icc 1 (P.k - 1),
      ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
          (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) =
      -((NrmDown P l π : ℂ) * (u - 1 + (rho P π l : ℂ))⁻¹) + (Nrm P l π : ℂ) * (u - 1 + ((rho P π l : ℂ) + 1))⁻¹ +
        (NrmDown P l π : ℂ) * (u + (rho P π l : ℂ))⁻¹ - (Nrm P l π : ℂ) * (u + ((rho P π l : ℂ) + 1))⁻¹ := by
    intro l hl
    rw [show u - 1 + ((rho P π l : ℂ) + 1) = u + rho P π l by ring,
      show u + ((rho P π l : ℂ) + 1) = u + rho P π l + 1 by ring,
      show u - 1 + (rho P π l : ℂ) = u + rho P π l - 1 by ring]
    have hx := mul_inv_cancel₀ (f1 l hl)
    have hy : (u + rho P π l + 1) * (u + rho P π l + 1)⁻¹ = 1 :=
      mul_inv_cancel₀ (fun h => f2 l hl (by linear_combination h))
    have hz : (u + rho P π l - 1) * (u + rho P π l - 1)⁻¹ = 1 :=
      mul_inv_cancel₀ (fun h => f0 l hl (by linear_combination h))
    have hxy : (u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹ = (u + rho P π l)⁻¹ - (u + rho P π l + 1)⁻¹ := by
      linear_combination (-(u + rho P π l + 1)⁻¹) * hx + (u + rho P π l)⁻¹ * hy
    have hxz : (u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹ = (u + rho P π l - 1)⁻¹ - (u + rho P π l)⁻¹ := by
      linear_combination (u + rho P π l - 1)⁻¹ * hx - (u + rho P π l)⁻¹ * hz
    linear_combination (Nrm P l π : ℂ) * hxy - (NrmDown P l π : ℂ) * hxz
  rw [Finset.sum_congr rfl T, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  have hTT : (P.TT : ℂ) = (P.T : ℂ) * P.T' := by unfold Par.TT; push_cast; ring
  rw [hTT]
  ring
end Formalism.FourierDecayAlt.P.Mx7
