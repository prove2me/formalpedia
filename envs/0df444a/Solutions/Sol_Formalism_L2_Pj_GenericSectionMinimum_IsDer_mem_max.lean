-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.IsDer.mem_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:44.486304+00:00
-- url     : https://prove2.me/submissions/b01bd2d4-863b-4659-9e0e-6944e9fe5548

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_der_zero
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_pow_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open Formalism.L2.Pj.GenericSectionMinimum.IsDer
variable {A : Type*} [CommRing A] {δ : A → A}
namespace Formalism.L2.Pj.GenericSectionMinimum.IsDer
theorem _root_.solution [IsArtinianRing A] (h : IsDer δ) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A)) (m : Ideal A)
    [hm : m.IsMaximal] {x : A} (hx : x ∈ m) : δ x ∈ m := by

  have hx' : algebraMap A (Localization.AtPrime m) x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m x).mpr hx
  have hnil : IsNilpotent (algebraMap A (Localization.AtPrime m) x) := by
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Localization.AtPrime m)
    refine ⟨k, ?_⟩
    have hj : algebraMap A (Localization.AtPrime m) x ∈ Ideal.jacobson (⊥ : Ideal (Localization.AtPrime m)) := by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    have := Ideal.pow_mem_pow hj k
    rwa [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  obtain ⟨n, hn⟩ := hnil
  rw [← map_pow] at hn
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) _).mp hn
  have hs' : s ∉ m := hs

  have hsx0 : (s * x) ^ (n + 1) ∈ (⊥ : Ideal A) := by
    rw [Ideal.mem_bot]
    calc (s * x) ^ (n + 1) = s ^ n * x * (s * x ^ n) := by ring
      _ = 0 := by simp only at hsx; rw [hsx, mul_zero]
  have hb : ∀ z ∈ (⊥ : Ideal A), δ z ∈ (⊥ : Ideal A) := by
    intro z hz
    rw [Ideal.mem_bot] at hz ⊢
    rw [hz, h.der_zero]
  have hd := h.pow_mem ⊥ hb hu hsx0
  rw [Ideal.mem_bot] at hd
  have hdm : δ (s * x) ∈ m := hm.isPrime.mem_of_pow_mem _ (by rw [hd]; exact m.zero_mem)
  rw [h.mul] at hdm
  have hxs : x * δ s ∈ m := m.mul_mem_right _ hx
  have hsd : s * δ x ∈ m := by
    have := m.sub_mem hdm hxs
    rwa [add_sub_cancel_right] at this
  exact (hm.isPrime.mem_or_mem hsd).resolve_left hs'
end Formalism.L2.Pj.GenericSectionMinimum.IsDer
