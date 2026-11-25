-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalDenominators.iF_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:24.486626+00:00
-- url     : https://prove2.me/submissions/71c6908f-461c-4443-b422-0ba55e5d0245

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LocalDenominators
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_val_iF_le
import Theorems.Thm_Formalism_L2_SG_Pf_LocalDenominators_val_unit

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
theorem _root_.solution {t : 𝓞 F} (ht : t ∉ p.asIdeal) : valuation A.Fp (A.ιF (t : F)) = 1 := by
  have h1 := (val_iF_le A (t : F) 1).mpr (by rw [map_one, val_unit ht])
  have h2 := (val_iF_le A 1 (t : F)).mpr (by rw [map_one, val_unit ht])
  rw [map_one, map_one] at h1 h2
  exact le_antisymm h1 h2
end Formalism.L2.SG.Pf.LocalDenominators
