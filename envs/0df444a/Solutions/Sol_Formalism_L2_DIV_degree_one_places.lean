-- Prove2me | solution 1 for Formalism.L2.DIV.degree_one_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:25:19.120072+00:00
-- url     : https://prove2.me/submissions/e2c9acc1-635f-4dd1-b353-0ad49bcca8e0

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
theorem _root_.solution : DegOnePlc := by
  intro F _ _ v hv
  have hp := hv.1
  have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := by
    have := Ideal.absNorm_mem v.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at this
    exact this
  have hd : plc v ∣ Ideal.absNorm v.asIdeal := ringChar.dvd h0
  have : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact absurd h (CharP.ringChar_ne_one (R := 𝓞 F ⧸ v.asIdeal))
  · exact h.symm
end Formalism.L2.DIV
