-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_keyNs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:37:41.115582+00:00
-- url     : https://prove2.me/submissions/25668d88-e5c5-4286-9d85-6864e035a250

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_mul_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_H_rtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_ss_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_mGG
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_projection_gamma_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_raising_constant_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_xEx_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_of_P
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_K_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_raising_projection
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_diagonal_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_left_raising_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_upper_lower_block_product
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_upper_block_product

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
    (hu : M.Up P l ρ ρ') :
    (SS l * proj κ ρ) * star (nabDef L0 κ b) - star (nabDef L0 κ b) * (SS l * proj κ ρ) -
      (L0.ζ * L0.GGi) * (SS l * proj κ ρ) = 0 := by
  set K := SS l * proj κ ρ with hK
  set Ns := star (nabDef L0 κ b) with hNs
  set W := L0.ζ * L0.GGi with hW
  set e := fun Y => M.xEx P {l} ρ Y with he
  have hPK : proj κ ρ' * K = K := by rw [hK, ← mul_assoc, pj_ss_pj κ hR hu]
  have hKGG : K * L0.GG = L0.GG * K := sc_K_comm h hSS l ρ (sc_mGG L0)
  have hKW : K * W = W * K := by
    have c1 : K * L0.ζ = L0.ζ * K := sc_K_comm h hSS l ρ (sc_mζ L0)
    have c2 : K * L0.GGi = L0.GGi * K := sc_K_comm h hSS l ρ (sc_mGGi L0)
    rw [hW, ← mul_assoc, c1, mul_assoc, c2, mul_assoc]
  have hKx : ∀ Y, K * xA κ Y = M.xC P ρ Y • K := by
    intro Y; rw [hK, mul_assoc, xA, pj_mul_kap, mul_smul_comm]
  have hH : ∀ Y, (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) * K - K * (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) =
      L0.GG * (M.xC P ρ' Y • ((sc_LL h hF).m0 Y * K) - M.xC P ρ Y • (K * (sc_LL h hF).m0 Y)) := by
    intro Y
    have hPm : proj κ ρ' * ((sc_LL h hF).m0 Y * K) = (sc_LL h hF).m0 Y * K := by
      rw [← mul_assoc, connection_raising_projection h hF, mul_assoc, hPK]
    have a1 : (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) * K = L0.GG * (M.xC P ρ' Y • ((sc_LL h hF).m0 Y * K)) := by
      rw [mul_assoc, mul_assoc, sc_x_of_P hPm]
    have a2 : K * (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) = L0.GG * (M.xC P ρ Y • (K * (sc_LL h hF).m0 Y)) := by
      calc K * (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) = (K * L0.GG) * xA κ Y * (sc_LL h hF).m0 Y := by
            simp only [mul_assoc]
        _ = L0.GG * (K * xA κ Y) * (sc_LL h hF).m0 Y := by rw [hKGG]; simp only [mul_assoc]
        _ = _ := by rw [hKx, mul_assoc, smul_mul_assoc]
    rw [a1, a2, mul_sub]
  set u : ℂ := Complex.I with hu'
  set v : ℂ := 2 * Complex.I with hv'
  have huim : u.im ≠ 0 := by simp [hu']
  have hvim : v.im ≠ 0 := by simp [hv']

  have hR1 : proj κ ρ' * ((u - v) • (QQ u 0 1 * QQ v 1 0 - QQ v 1 0 * QQ u 0 1)) * proj κ ρ =
      proj κ ρ' * (QQ u 1 1 * QQ v 0 0 - QQ v 1 1 * QQ u 0 0) * proj κ ρ := by rw [H_rtt h u v 0 1 1 0]
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, upper_lower_block_product h hF hR hl hu u v, lower_upper_block_product h hF hR hl hu u v,
    mul_sub, sub_mul, connection_diagonal_entry h, connection_diagonal_entry h, projection_gamma_coordinate h, projection_gamma_coordinate h, upper_left_raising_block h hF hR hSS hl hu hvim,
    upper_left_raising_block h hF hR hSS hl hu huim, ← smul_sub, ← hK, hH u] at hR1
  have c2 : (u - v) • (M.xEx P {l} ρ v • (M.xC P ρ' u • ((sc_LL h hF).m0 u * K) - M.xC P ρ u • (K * (sc_LL h hF).m0 u))) -
      ((M.xC P ρ' u * M.xEx P {l} ρ v) • ((sc_LL h hF).m0 (v + 1) * K) -
        (M.xC P ρ' v * M.xEx P {l} ρ u) • ((sc_LL h hF).m0 (u + 1) * K)) = 0 := by
    have c' : L0.GG * ((u - v) • (M.xEx P {l} ρ v • (M.xC P ρ' u • ((sc_LL h hF).m0 u * K) -
        M.xC P ρ u • (K * (sc_LL h hF).m0 u))) -
      ((M.xC P ρ' u * M.xEx P {l} ρ v) • ((sc_LL h hF).m0 (v + 1) * K) -
        (M.xC P ρ' v * M.xEx P {l} ρ u) • ((sc_LL h hF).m0 (u + 1) * K))) = 0 := by
      have e1 : L0.GG * ((u - v) • (M.xEx P {l} ρ v • (M.xC P ρ' u • ((sc_LL h hF).m0 u * K) -
          M.xC P ρ u • (K * (sc_LL h hF).m0 u))) -
        ((M.xC P ρ' u * M.xEx P {l} ρ v) • ((sc_LL h hF).m0 (v + 1) * K) -
          (M.xC P ρ' v * M.xEx P {l} ρ u) • ((sc_LL h hF).m0 (u + 1) * K))) =
        (u - v) • M.xEx P {l} ρ v • (L0.GG * (M.xC P ρ' u • ((sc_LL h hF).m0 u * K) -
          M.xC P ρ u • (K * (sc_LL h hF).m0 u))) -
        (M.xC P ρ' u • (L0.GG * M.xEx P {l} ρ v • ((sc_LL h hF).m0 (v + 1) * K)) -
          M.xC P ρ' v • (L0.GG * M.xEx P {l} ρ u • ((sc_LL h hF).m0 (u + 1) * K))) := by
        simp only [mul_sub, mul_smul_comm, smul_sub]; module
      rw [e1, hR1, sub_self]
    have := congrArg (fun X => L0.GGi * X) c'
    simp only [← mul_assoc, L0.GGi_GG, one_mul, mul_zero] at this
    exact this
  rw [sc_x_up hl hu u, sc_x_up hl hu v, sc_x_self hl ρ u, connection_raising_constant_eq, connection_raising_constant_eq, connection_raising_constant_eq] at c2
  have e2 : ∀ Y : ℂ, K * (-Ns - (Y - 1 / 2) • W) = -(K * Ns) - (Y - 1 / 2) • (W * K) := by
    intro Y; rw [mul_sub, mul_neg, mul_smul_comm, hKW]
  have e3 : ∀ Y : ℂ, (-Ns - (Y - 1 / 2) • W) * K = -(Ns * K) - (Y - 1 / 2) • (W * K) := by
    intro Y; rw [sub_mul, neg_mul, smul_mul_assoc]
  rw [e2, e3, e3, e3] at c2
  have c3 : (e u * e v * (u - v) * (u + (M.rho P ρ l : ℂ))) • (K * Ns - Ns * K - W * K) = 0 := by
    rw [← c2]; simp only [he]; module
  rcases smul_eq_zero.1 c3 with h0 | h0
  · exfalso
    have h1 : e u ≠ 0 := sc_xEx_ne P ρ {l} huim
    have h2 : e v ≠ 0 := sc_xEx_ne P ρ {l} hvim
    have h3 : u - v ≠ 0 := by
      rw [hu', hv']; intro h; have := congrArg Complex.im h; norm_num at this
    have h4 : u + (M.rho P ρ l : ℂ) ≠ 0 := by
      intro h; apply huim; have := congrArg Complex.im h; simpa using this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4 h0
  · exact h0
end Formalism.FourierDecayAlt.P.NFx2
