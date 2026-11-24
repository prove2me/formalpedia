-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.upper_lower_block_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:45.652377+00:00
-- url     : https://prove2.me/submissions/d7d959f3-cd82-47c7-acdc-f3c9bcafc336

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_not_up_down
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_upper_right_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_upper_right_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_G_pc
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_block_structure
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_raising_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_not_back
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_sum_block_structure
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_H_pc

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) {l : ℕ}
    (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ') (u w : ℂ) :
    proj κ ρ' * (QQ u 0 1 * QQ w 1 0) * proj κ ρ =
      M.xEx P {l} ρ w • ((L0.GG * xA κ u * (sc_LL h hF).m0 u) * (SS l * proj κ ρ)) := by
  have hne : ρ ≠ ρ' := up_ne P hl hu
  rw [connection_upper_right_eq h hF hR u, connection_lower_left_eq h hF hR w, connection_upper_right_entry, connection_lower_left_entry]
  set G1 := L0.GG * xA κ w * (sc_LL h hF).l0 w
  set S1 := ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ w)
  set H0 := L0.GG * xA κ u * (sc_LL h hF).m0 u
  set T0 := ∑ l ∈ Icc 1 (P.k - 1), (κ fun ρ => M.xEx P {l} ρ u) * star (SS l)
  have p1 : proj κ ρ' * (H0 * G1) * proj κ ρ = 0 := by
    refine blk_diag κ (X := H0 * G1) (fun σ => ?_) ρ' ρ hne
    show proj κ σ * (H0 * G1) = (H0 * G1) * proj κ σ
    rw [← mul_assoc, sc_H_pc h hF u σ, mul_assoc, sc_G_pc h hF w σ, ← mul_assoc]
  have p2 : proj κ ρ' * (H0 * S1) * proj κ ρ = M.xEx P {l} ρ w • (H0 * (SS l * proj κ ρ)) := by
    calc proj κ ρ' * (H0 * S1) * proj κ ρ = (proj κ ρ' * H0) * S1 * proj κ ρ := by simp only [mul_assoc]
      _ = H0 * (proj κ ρ' * S1 * proj κ ρ) := by
        rw [show proj κ ρ' * H0 = H0 * proj κ ρ' from sc_H_pc h hF u ρ']; simp only [mul_assoc]
      _ = _ := by rw [lower_sum_raising_block hR hl hu w, mul_smul_comm]
  have p3 : proj κ ρ' * (T0 * G1) * proj κ ρ = 0 := by
    calc proj κ ρ' * (T0 * G1) * proj κ ρ = proj κ ρ' * T0 * (G1 * proj κ ρ) := by simp only [mul_assoc]
      _ = (proj κ ρ' * T0 * proj κ ρ) * G1 := by
        rw [show G1 * proj κ ρ = proj κ ρ * G1 from (sc_G_pc h hF w ρ).symm]; simp only [mul_assoc]
      _ = 0 := by
        rw [upper_sum_block_structure h hR u ρ' ρ (fun ⟨j, _, hj⟩ => sc_not_back hl hu hj), zero_mul]
  have p4 : proj κ ρ' * (T0 * S1) * proj κ ρ = 0 := by
    refine blk_mul κ (upper_sum_block_structure h hR u) (lower_sum_block_structure hR w) ρ' ρ ?_
    rintro ⟨μ, ⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
    exact not_up_down P hi hj hl h1 h2 hu
  have : (H0 + T0) * (G1 + S1) = H0 * G1 + H0 * S1 + T0 * G1 + T0 * S1 := by noncomm_ring
  rw [this, mul_add, mul_add, mul_add, add_mul, add_mul, add_mul, p1, p2, p3, p4, zero_add, add_zero, add_zero]
end Formalism.FourierDecayAlt.P.NFx2
