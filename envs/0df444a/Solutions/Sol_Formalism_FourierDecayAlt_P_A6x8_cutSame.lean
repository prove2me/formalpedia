-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.cutSame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:34.83795+00:00
-- url     : https://prove2.me/submissions/a5dee78f-7208-4067-b3f1-68bff5216bba

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_small_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_I_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_adic_of_datum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_near_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_shift_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_shift_alg
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_root_near
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_inv_bounded

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
theorem _root_.solution : CutSame := by
  intro K _ _ _ R ψ hD hn m hm Om Sg hOm
  obtain ⟨hO, hC, hU, -⟩ := hOm
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨E, hE, hscale⟩ := small_scale hC hO
  obtain ⟨a, ha, hroot⟩ := h.root_near hn (m + 1) (by omega) hE
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg a
  obtain ⟨M, hM⟩ := h.inv_bounded hC hU
  have haR : (a : K) ∈ R := by
    obtain ⟨r, hr, e⟩ := ha
    rw [e]; exact R.mul_mem h.mem hr
  have step : ∀ A b : K, Near R (a : K) b → (∃ z ∈ Om, z ^ (m + 1) = A) →
      ∃ z ∈ Om, z ^ (m + 1) = A * b := by
    rintro A b hb ⟨z, hz, rfl⟩
    obtain ⟨κ, hκ, hκE⟩ := hroot b hb
    exact ⟨κ * z, hscale z hz κ hκE, by rw [mul_pow, hκ]; ring⟩
  refine ⟨V ∩ I R ((a * ϖ ^ (M * (m + 1)) : Kˣ) : K), inter_mem hV (I_nhds h.isOpen _),
    fun t ht => ⟨fun σ hσ t₁ hs => ?_, fun c hc r hr => ?_⟩⟩
  · have n1 : Near R (a : K) (1 + σ * (t : K)) := by
      obtain ⟨r, hr, e⟩ := hVs _ ht.1 σ hσ
      exact ⟨r, hr, by rw [e]⟩
    obtain ⟨v, hv, nv, -⟩ := h.near_inv ha n1
    have a1 := shift_alg t t₁ σ hs
    have e1 : (t₁ : K) = (t : K) * v := by linear_combination (-(t₁ : K)) * hv + v * a1
    ext c
    constructor
    · intro hc
      have := step ((-(t₁ : K)) ^ m * c) _ (n1.pow haR m) hc
      have e2 : (-(t₁ : K)) ^ m * c * (1 + σ * (t : K)) ^ m = (-(t : K)) ^ m * c := by
        have e3 : -(t : K) = -(t₁ : K) * (1 + σ * (t : K)) := by linear_combination a1
        rw [e3, mul_pow]; ring
      rwa [e2] at this
    · intro hc
      have := step ((-(t : K)) ^ m * c) _ (nv.pow haR m) hc
      have e2 : (-(t : K)) ^ m * c * v ^ m = (-(t₁ : K)) ^ m * c := by rw [e1]; ring
      rwa [e2] at this
  · obtain ⟨z, hz, e⟩ := hc
    obtain ⟨u, rfl⟩ := hU z hz
    have hb := hM _ hz ((u⁻¹ : Kˣ) : K) (by simp)
    obtain ⟨r1, hr1, et⟩ := ht.2
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    push_cast at et
    have htR : (t : K) ∈ R := by
      rw [et]; exact R.mul_mem (R.mul_mem haR (R.pow_mem h.mem _)) hr1
    have nb : Near R (a : K)
        (1 + (-(t : K)) ^ (m' + 1) * r * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1)) :=
      ⟨-(r1 * (-(t : K)) ^ m' * r * ((ϖ : K) ^ M * ((u⁻¹ : Kˣ) : K)) ^ (m' + 1 + 1)),
        R.neg_mem (R.mul_mem (R.mul_mem (R.mul_mem hr1 (R.pow_mem (R.neg_mem htR) _)) hr)
          (R.pow_mem hb _)), by
        linear_combination (-((-(t : K)) ^ m' * r * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1))) * et⟩
    have := step _ _ nb ⟨u, hz, rfl⟩
    have i1 : (u : K) ^ (m' + 1 + 1) * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1) = 1 := by
      rw [← mul_pow]; simp
    have e2 : (u : K) ^ (m' + 1 + 1) *
        (1 + (-(t : K)) ^ (m' + 1) * r * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1)) =
        (-(t : K)) ^ (m' + 1) * (c + r) := by
      linear_combination e + (-(t : K)) ^ (m' + 1) * r * i1
    rwa [e2] at this
end Formalism.FourierDecayAlt.P.A6x8
