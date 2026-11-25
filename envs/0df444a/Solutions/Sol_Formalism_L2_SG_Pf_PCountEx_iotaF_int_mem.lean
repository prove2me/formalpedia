-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.iotaF_int_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:58:05.40305+00:00
-- url     : https://prove2.me/submissions/7e40ac9c-cdf5-43d2-9669-b84f77d4e46c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IotaFIntMem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace Formalism.L2.SG.Pf.PCountEx
theorem _root_.solution (p : HeightOneSpectrum (𝓞 F)) (t : 𝓞 F) :
    (A p).ιF (algebraMap (𝓞 F) F t) ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) := by
  haveI := (A p).lf
  have h := ((A p).val (algebraMap (𝓞 F) F t) 1).2 (by simpa using p.valuation_le_one t)
  rw [map_one] at h
  rw [Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (ValuativeRel.valuation (A p).Fp)).1 h
end Formalism.L2.SG.Pf.PCountEx
