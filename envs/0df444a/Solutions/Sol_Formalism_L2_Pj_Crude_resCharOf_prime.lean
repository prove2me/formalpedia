-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.resCharOf_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:14.834925+00:00
-- url     : https://prove2.me/submissions/5933d121-4ef2-4a43-a983-83fd6ed0234f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
  {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K'] {ι : K →+* K'} {e : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution : (resCharOf la).Prime := by
  haveI := crv_finite la
  haveI : la.asIdeal.IsPrime := la.isPrime
  unfold resCharOf
  rcases CharP.char_is_prime_or_zero (𝓞 K ⧸ la.asIdeal) (ringChar (𝓞 K ⧸ la.asIdeal)) with hp | hp
  · exact hp
  · exact absurd hp (CharP.char_ne_zero_of_finite (𝓞 K ⧸ la.asIdeal) _)
end Formalism.L2.Pj.Crude
