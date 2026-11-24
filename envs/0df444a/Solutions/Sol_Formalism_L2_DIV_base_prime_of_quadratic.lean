-- Prove2me | solution 1 for Formalism.L2.DIV.base_prime_of_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:52.584065+00:00
-- url     : https://prove2.me/submissions/8f85b22b-6ff0-4b89-9e11-e7036915c4e8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_d_absNorm_eq
import Theorems.Thm_Formalism_L2_DIV_d_exists_place
import Theorems.Thm_Formalism_L2_DIV_d_key
import Theorems.Thm_Formalism_L2_DIV_IsBaseChar_good
import Theorems.Thm_Formalism_L2_DIV_Tup_good
import Theorems.Thm_Formalism_L2_DIV_mem_tupGrp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
namespace Formalism.L2.DIV
theorem _root_.solution (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) (hDO : DegOnePlc) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (_ : Module.finrank F E = 2) (L : Type) [Field L]
    (S : Set ℕ) (p : ℕ) (δ : Tup F E L S), IsBaseChar p (δ : Chr F E L) → p % 15 = 1 := by
  intro F E _ _ _ _ _ hdeg L _ S p δ h
  obtain ⟨v, hvp⟩ := d_exists_place F p h.1
  obtain ⟨⟨P, P', hne, hv⟩, hd1, _⟩ := IsBaseChar.good δ h v hvp
  have hm := (mem_tupGrp (δ : Chr F E L)).mp δ.2
  have ht := hm.2.2.1
  have hF := hm.2.1
  have hord := (h.2 v).1 hvp
  have hk := d_key hExU hW hA hC hO hEx hConj hdeg (δ : Chr F E L) ht hF v P P' hne hv (p - 1)
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = p := by
    have h1 := d_absNorm_eq hdeg hv
    rw [hDO F v hd1, hvp, Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    exact h1
  have hpow : resChar (δ : Chr F E L) P ^ (p - 1) = 1 := by
    apply MonoidHom.ext
    intro a
    rw [MonoidHom.pow_apply, ← map_pow, MonoidHom.one_apply]
    have ha : a ^ (p - 1) = 1 := by
      have := P.isMaximal
      let _ := Ideal.Quotient.field P.asIdeal
      have hc : Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = p - 1 :=
        (Nat.card_units (α := 𝓞 E ⧸ P.asIdeal)).trans (by rw [hcard])
      rw [← hc]
      exact pow_card_eq_one'
    rw [ha, map_one]
  have h15 : 15 ∣ p - 1 := (hord (p - 1)).mp (hk.mpr hpow)
  have h2 := h.1.two_le
  omega
end Formalism.L2.DIV
