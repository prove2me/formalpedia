-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:17:37.742464+00:00
-- url     : https://prove2.me/submissions/0050d034-c6b3-4fe0-96d6-587451fde161

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_coordinate_shift_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_e_other

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
theorem _root_.solution (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L)
    {QQ : ℂ → Matrix (Fin 2) (Fin 2) A}
    (h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y)
    (h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (hD3 : ∀ Y, QQ Y 0 0 * QQ (Y + 1) 1 1 - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y))
    (hD4 : ∀ Y, QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0) (hpoly : IsPF fun Y => QQ Y 0 0)
    {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) :
    M.qC P ((-(M.rho P τ l) - 1 : ℝ) : ℂ) • proj κ τ +
      sn_e P τ l ((-(M.rho P τ l) - 1 : ℝ) : ℂ) • (star (SS l) * SS l * proj κ τ) = 0 := by
  have r := sn_res hc hs h22 h21 h12 hD3 hD4 hpoly τ ((-(M.rho P τ l) - 1 : ℝ) : ℂ)
  have hx : M.xC P τ (((-(M.rho P τ l) - 1 : ℝ) : ℂ) + 1) = 0 := by
    rw [coordinate_shift_split hl]; apply mul_eq_zero_of_left; push_cast; ring
  rw [hx, zero_smul, zero_smul, zero_smul, add_zero, add_zero,
    Finset.sum_eq_single l (fun j hj hjl => by rw [sn_e_other hl hjl, zero_smul]) (fun h => absurd hl h),
    ← mul_smul_comm, ← mul_add] at r
  have := congrArg (L.GG * ·) r
  simp only [mul_zero, ← mul_assoc, L.GG_GGi, one_mul] at this
  rw [← this]
end Formalism.FourierDecayAlt.P.NFx2
