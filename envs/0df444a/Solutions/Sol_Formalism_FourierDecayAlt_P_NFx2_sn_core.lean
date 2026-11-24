-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:38:43.867163+00:00
-- url     : https://prove2.me/submissions/d0c1d4ff-eabc-4b20-b3e6-950cb3d7b088

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_mul_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_xA_xiA
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kG
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kappa_commute_raising
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_left_from_determinant
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_left_tail_projection

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
    (hD4 : ∀ Y, QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0)
    {Y : ℂ} (hY : Reg P Y) (hY1 : Reg P (Y + 1)) (τ : M.Ty P) :
    QQ Y 0 0 * proj κ τ = (M.qC P Y / M.xC P τ (Y + 1)) • (L.GGi * proj κ τ) + upperLeftTail L κ SS Y * proj κ τ +
      (L.GGi * (∑ j ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Y / (Y + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ)) +
        L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ)) := by
  have cG : ∀ Z, xA κ Z * L.GGi = L.GGi * xA κ Z := fun Z => (sn_kGi hc _).eq
  have cG' : ∀ Z, xiA κ Z * L.GG = L.GG * xiA κ Z := fun Z => (sn_kG hc _).eq
  have h1 : L.GG * xA κ (Y + 1) * (L.GGi * xiA κ (Y + 1)) = 1 := by
    calc L.GG * xA κ (Y + 1) * (L.GGi * xiA κ (Y + 1)) = L.GG * (xA κ (Y + 1) * L.GGi) * xiA κ (Y + 1) := by
          noncomm_ring
      _ = (L.GG * L.GGi) * (xA κ (Y + 1) * xiA κ (Y + 1)) := by rw [cG]; noncomm_ring
      _ = 1 := by rw [L.GG_GGi, xA_xiA κ hY1, one_mul]
  have h2 : L.GGi * xiA κ Y * (L.GG * xA κ Y) = 1 := by
    calc L.GGi * xiA κ Y * (L.GG * xA κ Y) = L.GGi * (xiA κ Y * L.GG) * xA κ Y := by noncomm_ring
      _ = (L.GGi * L.GG) * (xiA κ Y * xA κ Y) := by rw [cG']; noncomm_ring
      _ = 1 := by rw [L.GGi_GG, xiA_xA κ hY, one_mul]
  have d3 : QQ Y 0 0 * (L.GG * xA κ (Y + 1)) - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y) := by
    rw [← h22]; exact hD3 Y
  have d4 : QQ Y 1 0 * (L.GG * xA κ (Y + 1)) = (L.GG * xA κ Y) * QQ (Y + 1) 1 0 := by
    rw [← h22, ← h22]; exact hD4 Y
  have a3 := upper_left_from_determinant d3 d4 h1 h2
  have ex : QQ Y 0 1 * (L.GGi * xiA κ Y) * QQ Y 1 0 =
      upperLeftTail L κ SS Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * (L.GGi * xiA κ Y) *
        Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y := by
    rw [h12, h21, sn_expand L.GGi_GG (xA_xiA κ hY) (xiA_xA κ hY) (kappa_commute_raising hc _ Y).eq.symm (cG Y) (cG' Y)]
    unfold upperLeftTail; noncomm_ring
  have hq : algebraMap ℂ A (M.qC P Y) * (L.GGi * xiA κ (Y + 1)) * proj κ τ =
      (M.qC P Y / M.xC P τ (Y + 1)) • (L.GGi * proj κ τ) := by
    have e : xiA κ (Y + 1) * proj κ τ = (M.xC P τ (Y + 1))⁻¹ • proj κ τ := kap_mul_pj κ _ τ
    rw [mul_assoc, mul_assoc, e, mul_smul_comm, mul_smul_comm, ← Algebra.smul_def, smul_smul, div_eq_mul_inv,
      mul_comm (M.qC P Y)]
  rw [a3, ex, add_mul, add_mul, hq, upper_left_tail_projection hc hs hY τ]
  noncomm_ring
end Formalism.FourierDecayAlt.P.NFx2
