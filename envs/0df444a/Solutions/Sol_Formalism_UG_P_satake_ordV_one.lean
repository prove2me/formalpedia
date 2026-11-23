-- Prove2me | solution 1 for Formalism.UG.P.satake_ordV_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:14.813874+00:00
-- url     : https://prove2.me/submissions/4a7f73d5-1526-4e50-a7ea-43519ca6deea

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution : ordV F v 1 = 0 := by
  unfold ordV
  have h0 : Valued.v (1 : v.adicCompletion F) ≠ 0 := by simp
  rw [dif_neg h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [WithZero.coe_injective e]
  simp
end Formalism.UG.P
