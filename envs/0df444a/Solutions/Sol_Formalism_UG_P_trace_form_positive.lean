-- Prove2me | solution 1 for Formalism.UG.P.trace_form_positive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:27.388248+00:00
-- url     : https://prove2.me/submissions/ddd993f3-e414-44ad-94a0-3f468b29fa13

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsTrace
import Theorems.Thm_Formalism_UG_P_csTrace_trace_algebraMap_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CS.TracePos := by
  intro F E _ _ _ _ _ n _ _ σ J hJ
  obtain ⟨hF, hdef⟩ := hJ
  haveI : IsTotallyReal F := hF

  let φ0 : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  let ι0 : F →+* ℝ :=
    (NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (NumberField.InfinitePlace.mk φ0))).embedding
  have hval : ∀ x : n → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x := by
    intro x hx
    rcases hdef ι0 with h | h
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩

  have same : ∀ x y : n → E, x ≠ 0 → y ≠ 0 → ∀ a b : F,
      algebraMap F E a = hform (σ : E →+* E) J x x →
      algebraMap F E b = hform (σ : E →+* E) J y y → ∀ ι : F →+* ℝ, 0 < ι a * ι b := by
    intro x y hx hy a b ha hb ι
    rcases hdef ι with h | h
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos hap hbp
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos_of_neg_of_neg hap hbp
  by_cases hx : ∃ x0 : n → E, x0 ≠ 0
  · obtain ⟨x0, hx0⟩ := hx
    obtain ⟨a0, ha0⟩ := hval x0 hx0
    have ha0ne : a0 ≠ 0 := by
      intro h0
      have := same x0 x0 hx0 hx0 a0 a0 ha0 ha0 ι0
      rw [h0, map_zero, zero_mul] at this
      exact lt_irrefl _ this
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a0
    have hqF : algebraMap (𝓞 F) F q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (nonZeroDivisors.ne_zero hq)
    have hp : algebraMap (𝓞 F) F p = a0 * algebraMap (𝓞 F) F q := by
      rw [← hpq, div_mul_cancel₀ _ hqF]
    have hc : ((p * q : 𝓞 F) : F) = a0 * algebraMap (𝓞 F) F q * algebraMap (𝓞 F) F q := by
      have : ((p * q : 𝓞 F) : F) = algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F q := by
        rw [← map_mul]
      rw [this, hp]
    refine ⟨p * q, ?_, ?_⟩
    · intro h0
      have : ((p * q : 𝓞 F) : F) = 0 := by simp [h0]
      rw [hc] at this
      exact mul_ne_zero (mul_ne_zero ha0ne hqF) hqF this
    · intro x hx
      obtain ⟨a, ha⟩ := hval x hx
      rw [← ha, ← map_mul]
      apply csTrace_trace_algebraMap_pos
      intro ι
      have hs := same x0 x hx0 hx a0 a ha0 ha ι
      have hq2 : 0 < ι (algebraMap (𝓞 F) F q) * ι (algebraMap (𝓞 F) F q) :=
        mul_self_pos.mpr ((map_ne_zero_iff _ ι.injective).mpr hqF)
      rw [hc, map_mul, map_mul, map_mul]
      nlinarith [mul_pos hs hq2]
  · push_neg at hx
    refine ⟨1, one_ne_zero, fun x hx' => absurd (hx x) hx'⟩
end Formalism.UG.P
