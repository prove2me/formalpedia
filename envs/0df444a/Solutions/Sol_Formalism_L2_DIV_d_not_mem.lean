-- Prove2me | solution 1 for Formalism.L2.DIV.d_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:25:18.295001+00:00
-- url     : https://prove2.me/submissions/34d6aade-218a-42a2-81e6-611dc46844aa

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
set_option quotPrecheck false in
local notation "uIn" => Units.map (RInt F E).subtype.toMonoidHom
namespace Formalism.L2.DIV
theorem _root_.solution (hC : TpComap) (P : HeightOneSpectrum (𝓞 E)) (u : (RInt F E)ˣ) (b : 𝓞 E)
    (h : (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E)) : b ∉ P.asIdeal := by
  intro hb
  have h1 : toRInt F E b ∈ P.asIdeal.map (toRInt F E) := Ideal.mem_map_of_mem _ hb
  have h2 : (u : RInt F E) ∈ P.asIdeal.map (toRInt F E) := by
    have := add_mem h h1
    rwa [sub_add_cancel] at this
  have h3 : (1 : RInt F E) ∈ P.asIdeal.map (toRInt F E) := by
    have := Ideal.mul_mem_left _ ((u⁻¹ : (RInt F E)ˣ) : RInt F E) h2
    rwa [Units.inv_mul] at this
  have h4 : (1 : 𝓞 E) ∈ P.asIdeal := hC F E P 1 (by rw [map_one]; exact h3)
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h4)
end Formalism.L2.DIV
