-- Prove2me | solution 1 for Formalism.L2.Th1.H.UnitaryEighth_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:33:50.703725+00:00
-- url     : https://prove2.me/submissions/a44d628f-2e39-46ea-a256-185b4b6c1830

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_UnitaryEighthOf
import Theorems.Thm_Formalism_L2_Th1_H_cayleyDet
import Theorems.Thm_Formalism_L2_Th1_H_cosetRepsExist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (hC : UnitaryConstant) (hG : UnitaryGauss) (hI : UnitaryIndex) : UnitaryEighth := by
  intro V _ _ _ H Λ α δ Ae hL hU hAML θ hθ hθ0 c hc
  have hd : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0 := (LinearEquiv.isUnit_det' Ae).ne_zero
  obtain ⟨_, hidx⟩ := hI V H Λ α δ Ae hL hU
  have hne : relIdx (latA Λ δ Ae) Λ ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hidx
    have h1 : (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) ≠ 0 := by exact_mod_cast hU.idx₁
    exact mul_ne_zero h1 (pow_ne_zero _ (norm_ne_zero_iff.2 hd)) hidx.symm
  obtain ⟨S, hS⟩ := (cosetRepsExist V (latA Λ δ Ae) Λ hne).1
  have hc' := hC V H Λ α δ Ae hL hU hAML S hS θ hθ
  have hg := hG V H Λ α δ Ae hU S hS
  have hI0 : inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hc
    apply hθ0
    funext z
    have h1 := congrFun hc (δ z)
    simpa [pullInv] using h1
  have hceq : c = (‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)
      * gaussC H α Ae S := smul_left_injective ℂ hI0 (hc.symm.trans hc')
  have hdc := cayleyDet V H hU.herm hU.pos δ Ae hU.isom hU.cay
  rw [hceq, mul_pow, hg, mul_one, div_pow]
  generalize LinearMap.det (Ae : V →ₗ[ℂ] V) = d at *
  generalize LinearMap.det (δ : V →ₗ[ℂ] V) = D at *
  have hn2 : ((‖d‖ : ℝ) : ℂ) ^ 2 = d * conj d := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hs : ((-1 : ℂ) ^ Module.finrank ℂ V) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [show ((‖d‖ : ℝ) : ℂ) ^ 8 = (((‖d‖ : ℝ) : ℂ) ^ 2) ^ 4 by ring, hn2, hdc, div_eq_iff (pow_ne_zero _ hd)]
  linear_combination (D ^ 4 * d ^ 8) * hs
end Formalism.L2.Th1.H
