-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.upper_left_raising_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:44.521171+00:00
-- url     : https://prove2.me/submissions/120bc4b4-1800-44af-8315-41c9e1e3ef8b

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_orth
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_mul_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_not_up_down
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_quantum_determinant_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_ss_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_mGG
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_upper_right_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_upper_right_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_xEx_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_of_P
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_G_pc
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_block_structure
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_raising_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_K_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_not_back
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_sum_block_structure
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_raising_projection
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_H_pc
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_raising_gamma_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_diagonal_entry

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
theorem _root_.solution (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS)
    (hSS : ∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P}
    (hu : M.Up P l ρ ρ') {v : ℂ} (hv : v.im ≠ 0) :
    proj κ ρ' * QQ v 0 0 * proj κ ρ = M.xEx P {l} ρ v • ((sc_LL h hF).m0 (v + 1) * (SS l * proj κ ρ)) := by
  set K := SS l * proj κ ρ with hK
  set H := fun Y => L0.GG * xA κ Y * (sc_LL h hF).m0 Y with hHdef
  have hne : ρ ≠ ρ' := up_ne P hl hu
  have hPK : proj κ ρ' * K = K := by rw [hK, ← mul_assoc, pj_ss_pj κ hR hu]
  have hKGGi : K * L0.GGi = L0.GGi * K := sc_K_comm h hSS l ρ (sc_mGGi L0)

  have hB : proj κ ρ' * (QQ v 0 1 * QQ (v + 1) 1 0) * proj κ ρ = M.xEx P {l} ρ (v + 1) • (H v * K) := by
    rw [connection_upper_right_eq h hF hR v, connection_lower_left_eq h hF hR (v + 1), connection_upper_right_entry, connection_lower_left_entry]
    set G1 := L0.GG * xA κ (v + 1) * (sc_LL h hF).l0 (v + 1)
    set S1 := ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ (v + 1))
    set H0 := L0.GG * xA κ v * (sc_LL h hF).m0 v
    set T0 := ∑ l ∈ Icc 1 (P.k - 1), (κ fun ρ => M.xEx P {l} ρ v) * star (SS l)
    have p1 : proj κ ρ' * (H0 * G1) * proj κ ρ = 0 := by
      refine blk_diag κ (X := H0 * G1) (fun σ => ?_) ρ' ρ hne
      show proj κ σ * (H0 * G1) = (H0 * G1) * proj κ σ
      rw [← mul_assoc, sc_H_pc h hF v σ, mul_assoc, sc_G_pc h hF (v + 1) σ, ← mul_assoc]
    have p2 : proj κ ρ' * (H0 * S1) * proj κ ρ = M.xEx P {l} ρ (v + 1) • (H0 * K) := by
      calc proj κ ρ' * (H0 * S1) * proj κ ρ = (proj κ ρ' * H0) * S1 * proj κ ρ := by simp only [mul_assoc]
        _ = H0 * (proj κ ρ' * S1 * proj κ ρ) := by
          rw [show proj κ ρ' * H0 = H0 * proj κ ρ' from sc_H_pc h hF v ρ']; simp only [mul_assoc]
        _ = _ := by rw [lower_sum_raising_block hR hl hu (v + 1), mul_smul_comm]
    have p3 : proj κ ρ' * (T0 * G1) * proj κ ρ = 0 := by
      calc proj κ ρ' * (T0 * G1) * proj κ ρ = proj κ ρ' * T0 * (G1 * proj κ ρ) := by simp only [mul_assoc]
        _ = (proj κ ρ' * T0 * proj κ ρ) * G1 := by
          rw [show G1 * proj κ ρ = proj κ ρ * G1 from (sc_G_pc h hF (v + 1) ρ).symm]; simp only [mul_assoc]
        _ = 0 := by
          rw [upper_sum_block_structure h hR v ρ' ρ (fun ⟨j, _, hj⟩ => sc_not_back hl hu hj), zero_mul]
    have p4 : proj κ ρ' * (T0 * S1) * proj κ ρ = 0 := by
      refine blk_mul κ (upper_sum_block_structure h hR v) (lower_sum_block_structure hR (v + 1)) ρ' ρ ?_
      rintro ⟨μ, ⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
      exact not_up_down P hi hj hl h1 h2 hu
    have : (H0 + T0) * (G1 + S1) = H0 * G1 + H0 * S1 + T0 * G1 + T0 * S1 := by noncomm_ring
    rw [this, mul_add, mul_add, mul_add, add_mul, add_mul, add_mul, p1, p2, p3, p4, zero_add, add_zero, add_zero]

  have hD := quantum_determinant_relation h v
  have hq : proj κ ρ' * algebraMap ℂ A (M.qC P v) * proj κ ρ = 0 := by
    rw [← Algebra.commutes, mul_assoc, pj_orth κ hne.symm, mul_zero]
  have hL : proj κ ρ' * (QQ v 0 0 * QQ (v + 1) 1 1) * proj κ ρ =
      M.xC P ρ (v + 1) • (proj κ ρ' * QQ v 0 0 * proj κ ρ * L0.GG) := by
    rw [connection_diagonal_entry h, mul_assoc, mul_assoc, mul_assoc, xA, kap_mul_pj, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      ← sc_pf h ρ (sc_mGG L0)]
    noncomm_ring
  have hE : M.xC P ρ (v + 1) • (proj κ ρ' * QQ v 0 0 * proj κ ρ * L0.GG) =
      M.xEx P {l} ρ (v + 1) • (H v * K) := by
    rw [← hL, ← hB]
    have e : QQ v 0 0 * QQ (v + 1) 1 1 = QQ v 0 1 * QQ (v + 1) 1 0 + algebraMap ℂ A (M.qC P v) := by
      rw [← hD]; abel
    rw [e, mul_add, add_mul, hq, add_zero]

  have hHK : H v * K = M.xC P ρ' v • (L0.GG * ((sc_LL h hF).m0 v * K)) := by
    have hPm : proj κ ρ' * ((sc_LL h hF).m0 v * K) = (sc_LL h hF).m0 v * K := by
      rw [← mul_assoc, connection_raising_projection h hF, mul_assoc, hPK]
    simp only [hHdef]; rw [mul_assoc, mul_assoc, sc_x_of_P hPm, mul_smul_comm]
  rw [hHK, smul_smul, sc_x_self hl ρ (v + 1), sc_x_up hl hu v] at hE
  have hn1 : M.xEx P {l} ρ (v + 1) ≠ 0 := sc_xEx_ne P ρ {l} (by simpa using hv)
  have hn2 : (v + 1 + (M.rho P ρ l : ℂ)) ≠ 0 := by
    intro h0; apply hv; have := congrArg Complex.im h0; simpa using this
  have hE2 : proj κ ρ' * QQ v 0 0 * proj κ ρ * L0.GG = M.xEx P {l} ρ v • (L0.GG * ((sc_LL h hF).m0 v * K)) := by
    have hc : (v + 1 + (M.rho P ρ l : ℂ)) * M.xEx P {l} ρ (v + 1) ≠ 0 := mul_ne_zero hn2 hn1
    have := congrArg (fun X => ((v + 1 + (M.rho P ρ l : ℂ)) * M.xEx P {l} ρ (v + 1))⁻¹ • X) hE
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [this]; congr 1; field_simp; ring
  have := congrArg (fun X => X * L0.GGi) hE2
  simp only [mul_assoc, L0.GG_GGi, mul_one, smul_mul_assoc] at this
  rw [show proj κ ρ' * QQ v 0 0 * proj κ ρ = proj κ ρ' * (QQ v 0 0 * proj κ ρ) by rw [mul_assoc], this,
    ← connection_raising_gamma_shift h hF v, hKGGi]
  simp only [mul_assoc]
end Formalism.FourierDecayAlt.P.NFx2
