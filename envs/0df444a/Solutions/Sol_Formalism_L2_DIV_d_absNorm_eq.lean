-- Prove2me | solution 1 for Formalism.L2.DIV.d_absNorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:05:32.379176+00:00
-- url     : https://prove2.me/submissions/a8b3af77-a8e7-410d-a2d6-62531c17c1fd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_d_absNorm_map
import Theorems.Thm_Formalism_L2_DIV_d_absNorm_le

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
theorem _root_.solution (hdeg : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {P P' : HeightOneSpectrum (𝓞 E)}
    (hv : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  have hP := d_absNorm_le v P (d_under hv)
  have hP' := d_absNorm_le v P' (d_under (P := P') (P' := P) (by rw [hv, mul_comm]))
  have hmul := d_absNorm_map hdeg v
  rw [hv, map_mul] at hmul
  have hpos : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have h1 : Ideal.absNorm P.asIdeal * Ideal.absNorm v.asIdeal ≤
      Ideal.absNorm v.asIdeal * Ideal.absNorm v.asIdeal := by
    calc _ ≤ Ideal.absNorm P.asIdeal * Ideal.absNorm P'.asIdeal := Nat.mul_le_mul le_rfl hP'
      _ = _ := by rw [hmul, sq]
  exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hpos) hP
end Formalism.L2.DIV
