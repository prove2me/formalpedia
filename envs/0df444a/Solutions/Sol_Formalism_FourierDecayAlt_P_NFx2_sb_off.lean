-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:08:24.762797+00:00
-- url     : https://prove2.me/submissions/2f11134e-143d-4030-85e6-d316a45b59c9

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_pj_orth
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_feq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_type_eq_of_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_roots

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (h : SHyp P L0 QQ κ) (hP : P.OK) {σ ρ : M.Ty P} (hne : σ ≠ ρ) :
    (∀ v, lowerBlockAlt κ QQ σ ρ v = 0) ∨ ∃ m ∈ Icc 1 (P.k - 1), M.Up P m ρ σ ∧
      ∃ K : A, ∀ v, (v + ((M.rho P ρ m : ℝ) : ℂ) + 1) • lowerBlockAlt κ QQ σ ρ v = M.xC P σ v • K := by
  set T := lowerBlockAlt κ QQ σ ρ with hTdef
  set xs := M.xC P σ
  set xr := M.xC P ρ
  have O : ∀ u v, (u - v) • (xs u • T v - xr u • T v) = xs u • T v - xs v • T u := by
    intro u v
    have e := sb_feq h σ ρ u v
    rw [pj_orth κ hne, mul_zero, smul_zero, sub_zero] at e
    exact e
  have S : ∀ u v, (xs u - xr u) • T v = (xs v - xr v) • T u := by
    intro u v
    by_cases huv : u = v
    · subst huv; rfl
    · have e1 := O u v
      have e2 := O v u
      have : (u - v) • ((xs u - xr u) • T v - (xs v - xr v) • T u) = 0 := by
        linear_combination (norm := module) e1 + e2
      rcases smul_eq_zero.1 this with h0 | h0
      · exact absurd (sub_eq_zero.1 h0) huv
      · exact sub_eq_zero.1 h0
  by_cases hD : ∀ u, xs u - xr u = 0
  · exact absurd (type_eq_of_coordinate hP fun u => sub_eq_zero.1 (hD u)) hne
  push Not at hD
  obtain ⟨u0, hu0⟩ := hD
  set K := (xs u0 - xr u0)⁻¹ • T u0
  have hT : ∀ v, T v = (xs v - xr v) • K := by
    intro v
    have e := S u0 v
    have : T v = (xs u0 - xr u0)⁻¹ • ((xs u0 - xr u0) • T v) := by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]
    rw [this, e, smul_smul, smul_smul, mul_comm]
  by_cases hK : K = 0
  · left; intro v; rw [hT v, hK, smul_zero]
  right
  have hsc : ∀ u v, ((u - v) * (xs u - xr u) - xs u) * (xs v - xr v) + xs v * (xs u - xr u) = 0 := by
    intro u v
    have e := O u v
    rw [hT u, hT v] at e
    have : (((u - v) * (xs u - xr u) - xs u) * (xs v - xr v) + xs v * (xs u - xr u)) • K = 0 := by
      linear_combination (norm := module) e
    exact (smul_eq_zero.1 this).resolve_right hK
  set c0 := xs u0 / (xs u0 - xr u0) - u0
  have hxs : ∀ u, xs u = (xs u - xr u) * (u + c0) := by
    intro u
    have e := hsc u u0
    apply mul_right_cancel₀ hu0
    have hdc : xs u0 / (xs u0 - xr u0) * (xs u0 - xr u0) = xs u0 := div_mul_cancel₀ _ hu0
    simp only [c0]
    linear_combination -e - (xs u - xr u) * hdc
  have hc : ∀ u, xs u * (u + c0 - 1) = xr u * (u + c0) := by
    intro u
    have e := hxs u
    linear_combination (-1 : ℂ) * e
  obtain ⟨m, hm, hup, hcm⟩ := sb_roots hP hne hc
  refine ⟨m, hm, hup, K, fun v => ?_⟩
  rw [hT v, smul_smul]
  congr 1
  have e := hxs v
  rw [hcm] at e
  linear_combination (-1 : ℂ) * e
end Formalism.FourierDecayAlt.P.NFx2
