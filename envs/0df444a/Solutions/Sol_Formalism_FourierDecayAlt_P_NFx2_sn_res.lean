-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:46.67308+00:00
-- url     : https://prove2.me/submissions/92ec1deb-9f4d-49c7-9a76-5e481fb9dcc6

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_cpoly
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_isPF_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_regular_pairs_infinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_isPF_prod_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_quartic_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_polynomial_upper_left_tail
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_coordinate_shift_product
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_qeval
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_coordinate_shift_split
import Theorems.Thm_UpperTheory_Reformulated_B_IsPFSum_isPF_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) {QQ : ℂ → Matrix (Fin 2) (Fin 2) A}
    (h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y)
    (h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (hD3 : ∀ Y, QQ Y 0 0 * QQ (Y + 1) 1 1 - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y))
    (hD4 : ∀ Y, QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0) (hpoly : IsPF fun Y => QQ Y 0 0)
    (τ : M.Ty P) (Y : ℂ) :
    M.xC P τ (Y + 1) • (QQ Y 0 0 * proj κ τ) = M.qC P Y • (L.GGi * proj κ τ) +
      M.xC P τ (Y + 1) • (upperLeftTail L κ SS Y * proj κ τ) +
      (L.GGi * (∑ j ∈ Icc 1 (P.k - 1), sn_e P τ j Y • (star (SS j) * SS j * proj κ τ)) +
        M.xC P τ (Y + 1) • (L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ))) := by
  have pfx : ∀ {f : ℂ → A}, IsPF f → IsPF fun Y => M.xC P τ (Y + 1) • f Y := fun {f} hf => by
    simp_rw [coordinate_shift_product]; exact sn_isPF_prod_smul _ _ hf
  refine isPF_eq (f := fun Z => M.xC P τ (Z + 1) • (QQ Z 0 0 * proj κ τ))
    (g := fun Z => M.qC P Z • (L.GGi * proj κ τ) + M.xC P τ (Z + 1) • (upperLeftTail L κ SS Z * proj κ τ) +
      (L.GGi * (∑ j ∈ Icc 1 (P.k - 1), sn_e P τ j Z • (star (SS j) * SS j * proj κ τ)) +
        M.xC P τ (Z + 1) • (L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Z * proj κ τ))))
    (pfx (isPF_mul hpoly (isPF_const _))) ?_ (regular_pairs_infinite P) ?_ Y
  · refine isPF_add (isPF_add ?_ (pfx (isPF_mul polynomial_upper_left_tail (isPF_const _)))) (isPF_add ?_ ?_)
    · simp_rw [← sn_qeval]; exact isPF_cpoly _ _
    · refine isPF_mul (isPF_const _) (isPF_sum _ fun j _ => ?_)
      unfold sn_e; simp_rw [mul_smul]
      exact sn_isPF_prod_smul _ _ (sn_isPF_prod_smul _ _ (isPF_const _))
    · exact pfx (isPF_mul (isPF_const _) (isPF_mul polynomial_quartic_sum (isPF_const _)))
  · rintro Z ⟨hZ, hZ1⟩
    have hx : M.xC P τ (Z + 1) ≠ 0 := hZ1 τ
    rw [sn_core hc hs h22 h21 h12 hD3 hD4 hZ hZ1 τ, smul_add, smul_add, smul_smul, mul_div_cancel₀ _ hx,
      smul_add]
    congr 2
    rw [← mul_smul_comm, Finset.smul_sum]; congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [smul_smul]; congr 1
    have hx' := hx
    rw [coordinate_shift_split hj] at hx'
    have ha : Z + M.rho P τ j + 1 ≠ 0 := left_ne_zero_of_mul hx'
    rw [coordinate_shift_split hj, sn_e]; unfold M.xEx; field_simp
end Formalism.FourierDecayAlt.P.NFx2
