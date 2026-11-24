-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sc_keyN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:32:24.689649+00:00
-- url     : https://prove2.me/submissions/ae727a64-a5d3-4c26-baa7-8ffec82d0cf2

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_mul_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_left_commute_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_blk_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_ss_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_mGG
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lowering_projection
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lower_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_connection_lowering_eq_nabla
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_xEx_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_x_of_P
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_G_pc
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_raising_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_lower_sum_square_raising_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_K_comm

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
    (SS l * proj κ ρ) * nabDef L0 κ b - nabDef L0 κ b * (SS l * proj κ ρ) -
      (L0.ζb * L0.GGi) * (SS l * proj κ ρ) = 0 := by
  set K := SS l * proj κ ρ with hK
  set N := nabDef L0 κ b with hN
  set Z := L0.ζb * L0.GGi with hZ
  set G := fun Y => L0.GG * xA κ Y * (sc_LL h hF).l0 Y with hGdef
  set S := fun Y => ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y) with hSdef
  set e := fun Y => M.xEx P {l} ρ Y with he
  have hne : ρ ≠ ρ' := up_ne P hl hu
  have hPK : proj κ ρ' * K = K := by rw [hK, ← mul_assoc, pj_ss_pj κ hR hu]
  have hKGG : K * L0.GG = L0.GG * K := sc_K_comm h hSS l ρ (sc_mGG L0)
  have hKZ : K * Z = Z * K := by
    have c1 : K * L0.ζb = L0.ζb * K := sc_K_comm h hSS l ρ (sc_mζb L0)
    have c2 : K * L0.GGi = L0.GGi * K := sc_K_comm h hSS l ρ (sc_mGGi L0)
    rw [hZ, ← mul_assoc, c1, mul_assoc, c2, mul_assoc]
  have hKx : ∀ Y, K * xA κ Y = M.xC P ρ Y • K := by
    intro Y; rw [hK, mul_assoc, xA, pj_mul_kap, mul_smul_comm]
  have hG : ∀ Y, G Y * K - K * G Y =
      L0.GG * (M.xC P ρ' Y • ((sc_LL h hF).l0 Y * K) - M.xC P ρ Y • (K * (sc_LL h hF).l0 Y)) := by
    intro Y
    have hPl : proj κ ρ' * ((sc_LL h hF).l0 Y * K) = (sc_LL h hF).l0 Y * K := by
      rw [← mul_assoc, connection_lowering_projection h hF, mul_assoc, hPK]
    have a1 : G Y * K = L0.GG * (M.xC P ρ' Y • ((sc_LL h hF).l0 Y * K)) := by
      simp only [hGdef]; rw [mul_assoc, mul_assoc, sc_x_of_P hPl]
    have a2 : K * G Y = L0.GG * (M.xC P ρ Y • (K * (sc_LL h hF).l0 Y)) := by
      simp only [hGdef]
      calc K * (L0.GG * xA κ Y * (sc_LL h hF).l0 Y) = (K * L0.GG) * xA κ Y * (sc_LL h hF).l0 Y := by noncomm_ring
        _ = L0.GG * (K * xA κ Y) * (sc_LL h hF).l0 Y := by rw [hKGG]; noncomm_ring
        _ = _ := by rw [hKx, mul_assoc, smul_mul_assoc]
    rw [a1, a2, mul_sub]
  have hGP : ∀ Y σ, proj κ σ * G Y = G Y * proj κ σ := fun Y σ => sc_G_pc h hF Y σ
  have hT : ∀ u v, proj κ ρ' * (QQ u 1 0 * QQ v 1 0) * proj κ ρ = e v • (G u * K) + e u • (K * G v) := by
    intro u v
    rw [connection_lower_left_eq h hF hR u, connection_lower_left_eq h hF hR v, connection_lower_left_entry, connection_lower_left_entry]
    have p1 : proj κ ρ' * (G u * G v) * proj κ ρ = 0 := by
      refine blk_diag κ (X := G u * G v) (fun σ => ?_) ρ' ρ hne
      show proj κ σ * (G u * G v) = (G u * G v) * proj κ σ
      rw [← mul_assoc, hGP u σ, mul_assoc, hGP v σ, ← mul_assoc]
    have p2 : proj κ ρ' * (G u * S v) * proj κ ρ = e v • (G u * K) := by
      calc proj κ ρ' * (G u * S v) * proj κ ρ = (proj κ ρ' * G u) * S v * proj κ ρ := by noncomm_ring
        _ = G u * (proj κ ρ' * S v * proj κ ρ) := by rw [hGP]; noncomm_ring
        _ = _ := by rw [lower_sum_raising_block hR hl hu v, mul_smul_comm]
    have p3 : proj κ ρ' * (S u * G v) * proj κ ρ = e u • (K * G v) := by
      calc proj κ ρ' * (S u * G v) * proj κ ρ = proj κ ρ' * S u * (G v * proj κ ρ) := by noncomm_ring
        _ = (proj κ ρ' * S u * proj κ ρ) * G v := by rw [← hGP]; noncomm_ring
        _ = _ := by rw [lower_sum_raising_block hR hl hu u, smul_mul_assoc]
    have p4 : proj κ ρ' * (S u * S v) * proj κ ρ = 0 := lower_sum_square_raising_zero hR hl hu u v
    have : (G u + S u) * (G v + S v) = G u * G v + G u * S v + S u * G v + S u * S v := by noncomm_ring
    simp only [hGdef, hSdef] at this p1 p2 p3 p4 ⊢
    rw [this, mul_add, mul_add, mul_add, add_mul, add_mul, add_mul, p1, p2, p3, p4, zero_add, add_zero]
  have hC : ∀ u v, e v • (G u * K - K * G u) - e u • (G v * K - K * G v) = 0 := by
    intro u v
    have c := hT u v
    rw [(lower_left_commute_self h u v).eq, hT v u] at c
    rw [smul_sub, smul_sub]
    rw [show e v • (G u * K) - e v • (K * G u) - (e u • (G v * K) - e u • (K * G v)) =
      (e v • (G u * K) + e u • (K * G v)) - (e u • (G v * K) + e v • (K * G u)) by abel, c, sub_self]
  set u : ℂ := Complex.I with hu'
  set v : ℂ := 2 * Complex.I with hv'
  have c2 : e v • (M.xC P ρ' u • ((sc_LL h hF).l0 u * K) - M.xC P ρ u • (K * (sc_LL h hF).l0 u)) -
      e u • (M.xC P ρ' v • ((sc_LL h hF).l0 v * K) - M.xC P ρ v • (K * (sc_LL h hF).l0 v)) = 0 := by
    have c' : L0.GG * (e v • (M.xC P ρ' u • ((sc_LL h hF).l0 u * K) - M.xC P ρ u • (K * (sc_LL h hF).l0 u)) -
      e u • (M.xC P ρ' v • ((sc_LL h hF).l0 v * K) - M.xC P ρ v • (K * (sc_LL h hF).l0 v))) = 0 := by
      rw [mul_sub, mul_smul_comm, mul_smul_comm, ← hG u, ← hG v]; exact hC u v
    have := congrArg (fun X => L0.GGi * X) c'
    simp only [← mul_assoc, L0.GGi_GG, one_mul, mul_zero] at this
    exact this
  rw [sc_x_up hl hu u, sc_x_up hl hu v, sc_x_self hl ρ u, sc_x_self hl ρ v, connection_lowering_eq_nabla, connection_lowering_eq_nabla] at c2
  have e2 : ∀ Y : ℂ, K * (-N - (Y + 1 / 2) • Z) = -(K * N) - (Y + 1 / 2) • (Z * K) := by
    intro Y; rw [mul_sub, mul_neg, mul_smul_comm, hKZ]
  have e3 : ∀ Y : ℂ, (-N - (Y + 1 / 2) • Z) * K = -(N * K) - (Y + 1 / 2) • (Z * K) := by
    intro Y; rw [sub_mul, neg_mul, smul_mul_assoc]
  rw [e2, e2, e3, e3] at c2
  have c3 : (e u * e v * (u - v)) • (K * N - N * K - Z * K) = 0 := by
    rw [← c2]; simp only [he]; module
  rcases smul_eq_zero.1 c3 with h0 | h0
  · exfalso
    have h1 : e u ≠ 0 := sc_xEx_ne P ρ {l} (by simp [hu'])
    have h2 : e v ≠ 0 := sc_xEx_ne P ρ {l} (by simp [hv'])
    have h3 : u - v ≠ 0 := by
      rw [hu', hv']; intro h; have := congrArg Complex.im h; norm_num at this
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 h0
  · exact h0
end Formalism.FourierDecayAlt.P.NFx2
