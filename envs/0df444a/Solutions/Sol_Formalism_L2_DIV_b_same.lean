-- Prove2me | solution 1 for Formalism.L2.DIV.b_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:08:15.928439+00:00
-- url     : https://prove2.me/submissions/de399853-e247-4ec3-b130-d0f9a577d995

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_P2M_Formalism_L2_DIV_tpWild_proof__5005395ee64f

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
variable {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution (ξ : Chr F E L) (hξ : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (v : HeightOneSpectrum (𝓞 F)) (u u' : (RInt F E)ˣ)
    (hu : Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v)
    (hu' : Units.map (RInt F E).subtype.toMonoidHom u' ∈ suppAt E v)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (u : RInt F E) - u' ∈ P.asIdeal.map (toRInt F E)) :
    ξ (Units.map (RInt F E).subtype.toMonoidHom u) = ξ (Units.map (RInt F E).subtype.toMonoidHom u') := by
  have hw : Units.map (RInt F E).subtype.toMonoidHom (u * u'⁻¹) ∈ wildAt E v := by
    apply tpWild_proof'
    · rw [map_mul, map_inv]
      exact mul_mem hu (inv_mem hu')
    · intro P
      have : ((u * u'⁻¹ : (RInt F E)ˣ) : RInt F E) - 1 = ((u : RInt F E) - u') * ((u'⁻¹ : (RInt F E)ˣ) : RInt F E) := by
        rw [sub_mul, Units.mul_inv, Units.val_mul]
      rw [this]
      exact Ideal.mul_mem_right _ _ (h P)
  have h1 := hξ v hw
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one] at h1
  exact h1
end Formalism.L2.DIV
