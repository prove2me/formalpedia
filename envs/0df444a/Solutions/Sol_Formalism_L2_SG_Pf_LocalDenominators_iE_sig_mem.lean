-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalDenominators.iE_sig_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:53:58.394278+00:00
-- url     : https://prove2.me/submissions/9698a0f0-7af4-4888-ab6f-6573cee75e47

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
variable (hσ : ∀ e, sig (sig e) = e) (hfix : ∀ y : E, sig y = y → y ∈ (algebraMap F E).range)
include hσ hfix
namespace Formalism.L2.SG.Pf.LocalDenominators
theorem _root_.solution {x : E} (hx : A.ιE x ∈ A.O) : A.ιE (sig x) ∈ A.O := by
  rw [← A.cj_ιE]
  exact (A.O_def _).mpr
    (((A.O_def _).mp hx).map ((A.cj : A.Ep →ₐ[A.Fp] A.Ep).restrictScalars 𝒪[A.Fp]))
end Formalism.L2.SG.Pf.LocalDenominators
