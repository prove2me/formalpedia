-- Prove2me | solution 1 for Formalism.UG.P.csGlobApprox_vD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:55.475747+00:00
-- url     : https://prove2.me/submissions/f259444a-7dfe-4bb4-b268-707cb49e1543

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.UG.P
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
  first
  | exact (v.valuedAdicCompletion_eq_valuation r).trans (v.valuation_of_algebraMap r)
  | exact (v.valuedAdicCompletion_eq_valuation r).trans (v.valuation_of_algebraMap (K := F) r)
  | (rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
     exact (v.valuedAdicCompletion_eq_valuation' _).trans (v.valuation_of_algebraMap (K := F) r))
end Formalism.UG.P
