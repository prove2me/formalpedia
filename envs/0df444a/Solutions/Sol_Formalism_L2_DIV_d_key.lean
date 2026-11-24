-- Prove2me | solution 1 for Formalism.L2.DIV.d_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:25:59.994565+00:00
-- url     : https://prove2.me/submissions/15f53769-24a5-46fe-8b04-1ea8e0bf477f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_d_isRes
import Theorems.Thm_Formalism_L2_DIV_d_mem_intU
import Theorems.Thm_Formalism_L2_DIV_d_formula

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
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) (m : ℕ) :
    (∀ x ∈ inertAt E v, ξ x ^ m = 1) ↔ resChar ξ P ^ m = 1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro a
    obtain ⟨u1, b1, hb1, hs1, hc1, ho1⟩ := hExU F E P v (d_under hv) a
    have e1 := d_isRes hEx ξ ht P v (d_under hv) u1 a b1 hb1 hs1 hc1 ho1
    rw [MonoidHom.pow_apply, ← e1, MonoidHom.one_apply]
    exact h _ ⟨d_mem_intU u1, hs1⟩
  · intro h x hx
    obtain ⟨a, a'', e⟩ := d_formula hExU hW hA hC hO hEx hConj hdeg ξ ht hF v P P' hne hv x hx
    have h1 : ∀ c, resChar ξ P c ^ m = 1 := fun c => by
      rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]
    rw [e, mul_pow, inv_pow, h1, h1, inv_one, mul_one]
end Formalism.L2.DIV
