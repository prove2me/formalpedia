-- Prove2me | solution 1 for Formalism.L2.DIV.c_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:41.315519+00:00
-- url     : https://prove2.me/submissions/06b58c77-ead3-4b46-adb7-699f90ab3b83

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_c_lat_frac
import Theorems.Thm_Formalism_L2_DIV_c_decomp
import Theorems.Thm_Formalism_L2_DIV_pow_mem_integral_span
import Theorems.Thm_Formalism_L2_DIV_c_inv_pow_mem

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.DIV
theorem _root_.solution (x : (AfE F E)ˣ) :
    ∃ e : Eˣ, x ^ Fintype.card (ClassGroup (𝓞 E)) * (ratId F E e)⁻¹ ∈ intU F E := by
  classical
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  obtain ⟨_, _, e₂, h₂, hne, _⟩ := c_decomp x
  let I : FractionalIdeal (𝓞 E)⁰ E := ⟨c_lat x, c_lat_frac x⟩
  have hI : I ≠ 0 := by
    intro h0
    have : e₂ ∈ I := h₂
    rw [h0, FractionalIdeal.mem_zero_iff] at this
    exact hne this
  let U : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 I hI
  have h1 : ClassGroup.mk E (U ^ h) = 1 := by rw [map_pow, hh, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨⟨g, hg⟩⟩ := h1
  have hc : (((U ^ h : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) =
      (c_lat x) ^ h := by
    rw [Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]; rfl
  rw [hc] at hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h3 : e₂ ^ h ∈ (c_lat x) ^ h := Submodule.pow_mem_pow _ h₂ h
    rw [hg, Submodule.mem_span_singleton] at h3
    obtain ⟨b, hb⟩ := h3
    rw [smul_zero] at hb
    exact pow_ne_zero h hne hb.symm
  have hgm : g ∈ (c_lat x) ^ h := by rw [hg]; exact Submodule.mem_span_singleton_self g
  have hA := c_inv_pow_mem x h g hgm
  have hB : ∃ s ∈ RInt F E, (x : AfE F E) ^ h = ιE g * s := by
    have h4 := pow_mem_integral_span x h
    rw [hg] at h4
    refine Submodule.span_induction (p := fun z _ => ∃ s ∈ RInt F E, z = ιE g * s) ?_ ?_ ?_ ?_ h4
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      exact ⟨ιE (algebraMap _ _ b), Formalism.UG.CS.incl_int b, by rw [Algebra.smul_def, map_mul, mul_comm]⟩
    · exact ⟨0, zero_mem _, by simp⟩
    · rintro a b _ _ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
      exact ⟨s + s', add_mem hs hs', by ring⟩
    · rintro r a _ ⟨s, hs, rfl⟩
      exact ⟨r * s, mul_mem r.2 hs, by rw [Subring.smul_def, smul_eq_mul]; ring⟩
  obtain ⟨s, hs, hxs⟩ := hB
  have hv2 : ((ratId F E (Units.mk0 g hg0) : (AfE F E)ˣ) : AfE F E) = ιE g := rfl
  have hv1 : (((ratId F E (Units.mk0 g hg0))⁻¹ : (AfE F E)ˣ) : AfE F E) = ιE g⁻¹ := by
    rw [← map_inv]
    show ιE (((Units.mk0 g hg0)⁻¹ : Eˣ) : E) = ιE g⁻¹
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
  refine ⟨Units.mk0 g hg0, ?_⟩
  rw [intU, Submonoid.mem_units_iff]
  constructor
  · rw [Units.val_mul, Units.val_pow_eq_pow_val, hv1, hxs]
    have : ιE g * s * ιE g⁻¹ = s := by
      have h5 : ιE g * ιE g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hg0, map_one]
      linear_combination s * h5
    rw [this]; exact hs
  · rw [mul_inv, inv_inv, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val, hv2]
    exact hA
end Formalism.L2.DIV
