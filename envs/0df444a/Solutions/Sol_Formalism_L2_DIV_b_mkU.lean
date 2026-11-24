-- Prove2me | solution 1 for Formalism.L2.DIV.b_mkU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:34:23.810204+00:00
-- url     : https://prove2.me/submissions/64d508a5-7758-461f-9735-13c1589bc28a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_eps_idem
import Theorems.Thm_Formalism_L2_DIV_b_loc_inv

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
namespace Formalism.L2.DIV
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (b c : 𝓞 E) (r : 𝓞 F) (hr : r ∉ v.asIdeal)
    (hbc : b * c = algebraMap (𝓞 F) (𝓞 E) r) :
    ∃ u : (RInt F E)ˣ, (u : RInt F E) = toRInt F E b * bEps E v + (1 - bEps E v) := by
  obtain ⟨ρ, hρ⟩ := b_loc_inv (E := E) v r hr
  have hi := b_eps_idem (E := E) v
  rw [← hbc, map_mul] at hρ
  refine ⟨⟨toRInt F E b * bEps E v + (1 - bEps E v), toRInt F E c * ρ * bEps E v + (1 - bEps E v), ?_, ?_⟩, rfl⟩
  · have : (toRInt F E b * bEps E v + (1 - bEps E v)) * (toRInt F E c * ρ * bEps E v + (1 - bEps E v)) =
        (toRInt F E b * toRInt F E c * ρ) * (bEps E v * bEps E v) + 1 - 2 * bEps E v + bEps E v * bEps E v +
          (toRInt F E b + toRInt F E c * ρ) * (bEps E v - bEps E v * bEps E v) := by ring
    rw [this, hρ, hi, hi]; ring
  · have : (toRInt F E c * ρ * bEps E v + (1 - bEps E v)) * (toRInt F E b * bEps E v + (1 - bEps E v)) =
        (toRInt F E b * toRInt F E c * ρ) * (bEps E v * bEps E v) + 1 - 2 * bEps E v + bEps E v * bEps E v +
          (toRInt F E b + toRInt F E c * ρ) * (bEps E v - bEps E v * bEps E v) := by ring
    rw [this, hρ, hi, hi]; ring
end Formalism.L2.DIV
