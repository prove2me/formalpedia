-- Prove2me | solution 1 for Formalism.UG.P.cartan_unif_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:16.319921+00:00
-- url     : https://prove2.me/submissions/0c5291d5-5547-4077-8978-67e619cee33b

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open IsDedekindDomain NumberField
namespace Formalism.UG.P
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletion F) (h : IsUnifV F v ϖ) : ϖ ≠ 0 := by
  unfold IsUnifV at h
  intro h0
  rw [h0, map_zero] at h
  exact WithZero.coe_ne_zero h.symm
end Formalism.UG.P
