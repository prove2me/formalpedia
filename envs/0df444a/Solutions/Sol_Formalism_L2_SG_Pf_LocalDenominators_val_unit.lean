-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalDenominators.val_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:24.688884+00:00
-- url     : https://prove2.me/submissions/1ba3accc-18b1-4f37-9198-ad9b1ed395c0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LocalDenominators
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_val_int_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel Polynomial
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalDenominators
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace Formalism.L2.SG.Pf.LocalDenominators
theorem _root_.solution {t : 𝓞 F} (ht : t ∉ p.asIdeal) : p.valuation F (t : F) = 1 := by
  refine le_antisymm (val_int_le t) (not_lt.mp fun h => ht ?_)
  first
  | exact (p.valuation_lt_one_iff_mem t).mp h
  | exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) p t).mp h
end Formalism.L2.SG.Pf.LocalDenominators
