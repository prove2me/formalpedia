-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.rootCorr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:35.255801+00:00
-- url     : https://prove2.me/submissions/38d147b6-0aa8-4633-8412-7ef96e18793a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_adic_of_datum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_near_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_shift_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_shift_alg
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_root_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
namespace Formalism.FourierDecayAlt.P.A6x8
theorem _root_.solution : RootCorr := by
  intro K _ _ _ R ψ hD hn m Sg E hE
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨a, ha, hroot⟩ := h.root_near hn (m + 1) (by omega) hE
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg a
  refine ⟨V, hV, fun t t₁ t₂ ht σ hσ σ' hσ' hs hs' => ?_⟩
  have haR : (a : K) ∈ R := by
    obtain ⟨r, hr, e⟩ := ha
    rw [e]; exact R.mul_mem h.mem hr
  have n1 : Near R (a : K) (1 + σ * (t : K)) := by
    obtain ⟨r, hr, e⟩ := hVs _ ht σ hσ
    exact ⟨r, hr, by rw [e]⟩
  have n2 : Near R (a : K) (1 + σ' * (t : K)) := by
    obtain ⟨r, hr, e⟩ := hVs _ ht σ' hσ'
    exact ⟨r, hr, by rw [e]⟩
  obtain ⟨v, hv, nv, -⟩ := h.near_inv ha n2
  have a1 := shift_alg t t₁ σ hs
  have a2 := shift_alg t t₂ σ' hs'
  have hr : ((t₂ * t₁⁻¹ : Kˣ) : K) = (1 + σ * (t : K)) * v := by
    have i1 : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := by simp
    rw [Units.val_mul]
    linear_combination (-((t₂ : K) * ((t₁⁻¹ : Kˣ) : K))) * hv + ((t₁⁻¹ : Kˣ) : K) * v * a2 -
      ((t₁⁻¹ : Kˣ) : K) * v * a1 + (1 + σ * (t : K)) * v * i1
  obtain ⟨κ, hκ, hκE⟩ := hroot _ ((n1.mul haR nv).pow haR m)
  rw [← hr, ← Units.val_pow_eq_pow_val] at hκ
  have hu : IsUnit κ := by
    have : IsUnit (κ ^ (m + 1)) := by rw [hκ]; exact Units.isUnit _
    exact (isUnit_pow_iff (by omega)).1 this
  obtain ⟨κ', rfl⟩ := hu
  exact ⟨κ', Units.ext (by rw [Units.val_pow_eq_pow_val, hκ]), hκE⟩
end Formalism.FourierDecayAlt.P.A6x8
