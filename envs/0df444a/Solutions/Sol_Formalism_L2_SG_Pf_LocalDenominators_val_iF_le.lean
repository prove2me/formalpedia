-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalDenominators.val_iF_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:34.364862+00:00
-- url     : https://prove2.me/submissions/a4d03d1d-0401-430b-9d4f-81f5ec85c104

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsDenOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LocalDenominators

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
theorem _root_.solution (a b : F) :
    valuation A.Fp (A.ιF a) ≤ valuation A.Fp (A.ιF b) ↔ p.valuation F a ≤ p.valuation F b := by
  first
  | exact ((Valuation.Compatible.vle_iff_le (v := valuation A.Fp) _ _).symm).trans (A.val a b)
  | exact ((Valuation.Compatible.vle_iff_le _ _).symm).trans (A.val a b)
end Formalism.L2.SG.Pf.LocalDenominators
