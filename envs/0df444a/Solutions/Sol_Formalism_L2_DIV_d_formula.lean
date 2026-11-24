-- Prove2me | solution 1 for Formalism.L2.DIV.d_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:04:32.647417+00:00
-- url     : https://prove2.me/submissions/3de08a1b-1480-412d-94e1-b8f880e062f8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_d_res_one
import Theorems.Thm_Formalism_L2_DIV_d_isRes
import Theorems.Thm_Formalism_L2_DIV_d_isUnit_mk
import Theorems.Thm_Formalism_L2_DIV_d_lift_intU
import Theorems.Thm_Formalism_L2_DIV_d_not_mem
import Theorems.Thm_Formalism_L2_DIV_d_other

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
set_option quotPrecheck false in
local notation "uIn" => Units.map (RInt F E).subtype.toMonoidHom
namespace Formalism.L2.DIV
theorem _root_.solution (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) (hdeg : Module.finrank F E = 2)
    (ξ : Chr F E L) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) (hF : (idF F E).range ≤ ξ.ker)
    (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)) (hne : P ≠ P')
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal)
    (x : (AfE F E)ˣ) (hx : x ∈ inertAt E v) :
    ∃ a a'' : (𝓞 E ⧸ P.asIdeal)ˣ, ξ x = resChar ξ P a * (resChar ξ P a'')⁻¹ := by
  have hv' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P'.asIdeal * P.asIdeal := by rw [hv, mul_comm]
  have hPv := d_under hv
  have hPv' := d_under hv'
  obtain ⟨u, rfl⟩ := d_lift_intU hx.1
  have hsu := hx.2
  obtain ⟨b, hb⟩ := hA F E P (u : RInt F E)
  obtain ⟨b', hb'⟩ := hA F E P' (u : RInt F E)
  obtain ⟨n, hn⟩ := d_res_one hdeg hv' b'
  have hun : (u : RInt F E) - toRInt F E (algebraMap (𝓞 F) (𝓞 E) n) ∈ P'.asIdeal.map (toRInt F E) := by
    have h1 : toRInt F E (b' - algebraMap (𝓞 F) (𝓞 E) n) ∈ P'.asIdeal.map (toRInt F E) :=
      Ideal.mem_map_of_mem _ hn
    have h2 := add_mem hb' h1
    rw [map_sub] at h2
    convert h2 using 1
    ring
  have hbP := d_not_mem hC P u b hb
  have hnP' := d_not_mem hC P' u _ hun
  have hnv : n ∉ v.asIdeal := by
    intro h
    apply hnP'
    rw [← hPv'] at h
    exact h
  have hnP : algebraMap (𝓞 F) (𝓞 E) n ∉ P.asIdeal := by
    intro h
    apply hnv
    rw [← hPv]
    exact h
  obtain ⟨a, ha⟩ := d_isUnit_mk P hbP
  obtain ⟨a', ha'⟩ := d_isUnit_mk P' hnP'
  obtain ⟨a'', ha''⟩ := d_isUnit_mk P hnP
  have hc := hConj F E L ξ ht hF v P P' hne hv n a'' a' ha'' ha'
  obtain ⟨u1, b1, hb1, hs1, hc1, ho1⟩ := hExU F E P v hPv a
  obtain ⟨u2, b2, hb2, hs2, hc2, ho2⟩ := hExU F E P' v hPv' a'
  have e1 : ξ (uIn u1) = resChar ξ P a := d_isRes hEx ξ ht P v hPv u1 a b1 hb1 hs1 hc1 ho1
  have e2 : ξ (uIn u2) = resChar ξ P' a' := d_isRes hEx ξ ht P' v hPv' u2 a' b2 hb2 hs2 hc2 ho2
  have hdiff : ∀ Q : HeightOneSpectrum (𝓞 E), (u : RInt F E) - u1 * u2 ∈ Q.asIdeal.map (toRInt F E) := by
    intro Q
    by_cases h1 : Q = P
    · subst h1
      have t2 := Ideal.mul_mem_right (u2 : RInt F E) _ hc1
      have t3 := Ideal.mul_mem_left _ (toRInt F E b1) (ho2 Q hne)
      have t4 : toRInt F E (b1 - b) ∈ Q.asIdeal.map (toRInt F E) :=
        Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.mp (hb1.trans ha))
      have t := sub_mem (sub_mem (sub_mem hb t2) t3) t4
      rw [map_sub] at t
      convert t using 1
      ring
    · by_cases h2 : Q = P'
      · subst h2
        have t2 := Ideal.mul_mem_right (u1 : RInt F E) _ hc2
        have t3 := Ideal.mul_mem_left _ (toRInt F E b2) (ho1 Q hne.symm)
        have t4 : toRInt F E (b2 - algebraMap (𝓞 F) (𝓞 E) n) ∈ Q.asIdeal.map (toRInt F E) :=
          Ideal.mem_map_of_mem _ (Ideal.Quotient.eq.mp (hb2.trans ha'))
        have t := sub_mem (sub_mem (sub_mem hun t2) t3) t4
        rw [map_sub] at t
        convert t using 1
        ring
      · have hQ := d_other hv h1 h2
        have t1 := hO F E v Q hQ u hsu
        have t2 := Ideal.mul_mem_right (u2 : RInt F E) _ (hO F E v Q hQ u1 hs1)
        have t3 := hO F E v Q hQ u2 hs2
        have t := sub_mem (sub_mem t1 t2) t3
        convert t using 1
        ring
  have hw : uIn (u * (u1 * u2)⁻¹) ∈ wildAt E v := by
    apply hW F E v
    · rw [map_mul, map_inv, map_mul]
      exact mul_mem hsu (inv_mem (mul_mem hs1 hs2))
    · intro Q
      have h1 : ((u * (u1 * u2)⁻¹ : (RInt F E)ˣ) : RInt F E) - 1 =
          ((u : RInt F E) - u1 * u2) * (((u1 * u2)⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        rw [sub_mul, Units.val_mul, ← Units.val_mul u1 u2, Units.mul_inv]
      rw [h1]
      exact Ideal.mul_mem_right _ _ (hdiff Q)
  have hk : ξ (uIn (u * (u1 * u2)⁻¹)) = 1 := MonoidHom.mem_ker.mp (ht v hw)
  simp only [map_mul, map_inv] at hk
  rw [e1, e2] at hk
  refine ⟨a, a'', ?_⟩
  rw [mul_inv_eq_one.mp hk, eq_inv_of_mul_eq_one_right hc]
end Formalism.L2.DIV
