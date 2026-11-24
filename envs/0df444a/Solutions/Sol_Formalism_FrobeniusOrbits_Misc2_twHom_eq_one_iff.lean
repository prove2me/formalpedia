-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Misc2.twHom_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:35:45.522599+00:00
-- url     : https://prove2.me/submissions/a9904e99-5445-4cc9-bb75-9f8ff13cc633

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_chC_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_int_units_sq_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Misc2
open Formalism.FrobeniusOrbits.Misc2
namespace Formalism.FrobeniusOrbits.Misc2
theorem _root_.solution (e : ℕ) (χ : GG e →* ℂˣ) : twHom e χ = 1 ↔ χ = chC e := by
  constructor
  · intro h
    ext g
    have := DFunLike.congr_fun h g
    simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.one_apply, chC_apply] at this
    have h2 : starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = (((g.1.2 : ℤˣ) : ℤ) : ℂ) := by
      have := congrArg (fun z => (((g.1.2 : ℤˣ) : ℤ) : ℂ) * z) this
      simp only [← mul_assoc, int_units_sq_C, one_mul, mul_one] at this
      exact this
    have := congrArg (starRingEnd ℂ) h2
    rw [chC_apply]
    simpa using this
  · rintro rfl
    ext g
    simp only [twHom, conjHom, MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      Units.coeHom_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MonoidHom.one_apply, chC_apply]
    simp [int_units_sq_C]
end Formalism.FrobeniusOrbits.Misc2
