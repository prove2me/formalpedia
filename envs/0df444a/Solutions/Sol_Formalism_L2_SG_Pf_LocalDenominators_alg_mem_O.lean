-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:52.275799+00:00
-- url     : https://prove2.me/submissions/f35a2374-0931-459f-92f2-5d1c03f8da93

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
theorem _root_.solution {z : A.Fp} (hz : z ∈ 𝒪[A.Fp]) : algebraMap A.Fp A.Ep z ∈ A.O := by
  refine (A.O_def _).mpr ?_
  exact isIntegral_algebraMap (x := (⟨z, hz⟩ : 𝒪[A.Fp]))
end Formalism.L2.SG.Pf.LocalDenominators
