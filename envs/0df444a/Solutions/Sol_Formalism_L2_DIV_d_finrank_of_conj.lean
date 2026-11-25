-- Prove2me | solution 1 for Formalism.L2.DIV.d_finrank_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:04.515364+00:00
-- url     : https://prove2.me/submissions/d4430b1a-7f37-435c-984b-390bc182a07f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP

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
theorem _root_.solution {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsConjOf σ) : Module.finrank F E = 2 := by
  obtain ⟨hne, hinv, hfix⟩ := h
  have hex : ∃ e, σ e ≠ e := by
    by_contra hc
    push Not at hc
    exact hne (AlgHom.ext hc)
  obtain ⟨e0, he0⟩ := hex
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = e0 - σ e0 := ⟨_, rfl⟩
  have hθ0 : θ ≠ 0 := fun h => he0 (sub_eq_zero.mp (hθ ▸ h)).symm
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hinv]; ring
  have h2 : (2 : E) ≠ 0 := by
    have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
    exact two_ne_zero
  have h2' : algebraMap F E 2 = 2 := map_ofNat _ 2
  let f : (F × F) →ₗ[F] E := LinearMap.coprod (Algebra.linearMap F E) (LinearMap.toSpanSingleton F E θ)
  have hf : ∀ a b, f (a, b) = algebraMap F E a + b • θ := fun a b => by simp [f]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hf] at hab
    have hab' : algebraMap F E a - b • θ = 0 := by
      have := congrArg σ hab
      rw [map_add, map_smul, hσθ, AlgHom.commutes, map_zero, smul_neg] at this
      rw [sub_eq_add_neg]
      exact this
    have ha : algebraMap F E a = 0 := by
      have : (2 : E) * algebraMap F E a = 0 := by linear_combination hab + hab'
      exact (mul_eq_zero.mp this).resolve_left h2
    have hb : b • θ = 0 := by rw [ha, zero_add] at hab; exact hab
    have ha' : a = 0 := (map_eq_zero _).mp ha
    have hb' : b = 0 := (smul_eq_zero.mp hb).resolve_right hθ0
    rw [ha', hb']
    rfl
  have hsurj : Function.Surjective f := by
    intro e
    obtain ⟨a, ha⟩ := hfix (e + σ e) (by rw [map_add, hinv]; ring)
    obtain ⟨b, hb⟩ := hfix ((e - σ e) / θ) (by
      rw [map_div₀, map_sub, hinv, hσθ, div_neg, ← neg_div, neg_sub])
    refine ⟨(a / 2, b / 2), ?_⟩
    rw [hf, Algebra.smul_def, map_div₀, map_div₀, ha, hb, h2']
    field_simp
    ring
  have hfin := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [← hfin, Module.finrank_prod, Module.finrank_self]
end Formalism.L2.DIV
