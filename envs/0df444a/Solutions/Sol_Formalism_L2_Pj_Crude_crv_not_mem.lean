-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crv_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:27.5958+00:00
-- url     : https://prove2.me/submissions/c65e5f8e-53f6-445b-9acf-70bebbcb7fb0

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal

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
theorem _root_.solution {m : ℕ} (hm : ¬ resCharOf la ∣ m) : ((m : ℕ) : 𝓞 K) ∉ la.asIdeal := by
  intro hmem
  apply hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
  unfold resCharOf
  exact ringChar.dvd hmem
end Formalism.L2.Pj.Crude
