-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crv_nval_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:57.463944+00:00
-- url     : https://prove2.me/submissions/f2e90a1f-0924-4096-89ca-7d17ba43cf2e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_vLa_natCast

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
theorem _root_.solution (ho : OverLa la V ι e) {N : ℕ} (hN : N ≠ 0) :
    nval V e ((N : ℕ) : K') = (((padicValNat (resCharOf la) N * ramOverZ la : ℕ) : ℝ) : EReal) := by
  unfold nval OverLa at *
  have hN' : ((N : ℕ) : K') ≠ 0 := by
    rw [← map_natCast ι N]
    exact (map_ne_zero ι).mpr (Nat.cast_ne_zero.mpr hN)
  rw [if_neg hN', ← map_natCast ι N, ho.2, crv_vLa_natCast la hN]
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  congr 1
  generalize padicValNat (resCharOf la) N * ramOverZ la = m
  push_cast
  rw [div_eq_iff he]
  ring
end Formalism.L2.Pj.Crude
