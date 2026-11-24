-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crv_vLa_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:14:41.606149+00:00
-- url     : https://prove2.me/submissions/62efca28-5dc8-4667-b372-e42ef609fdeb

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_not_mem
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_vLa_natCast_eq

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
theorem _root_.solution {m : ℕ} (hm : ¬ resCharOf la ∣ m) : vLa la ((m : ℕ) : K) = 0 := by
  rw [crv_vLa_natCast_eq]
  have h1 : la.intValuation (m : 𝓞 K) = 1 := by
    rcases (la.intValuation_le_one (m : 𝓞 K)).lt_or_eq with hlt | heq
    · exact absurd ((la.intValuation_lt_one_iff_mem _).mp hlt) (crv_not_mem la hm)
    · exact heq
  rw [h1, WithZero.log_one, neg_zero]
end Formalism.L2.Pj.Crude
