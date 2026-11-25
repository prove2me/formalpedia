-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.iotaE_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:45.667772+00:00
-- url     : https://prove2.me/submissions/55ef3e19-c1ac-43a8-af94-df5e83d28e7d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SimpLemmas
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace Formalism.L2.SG.Pf.PCountEx
theorem _root_.solution (p : HeightOneSpectrum (𝓞 F)) (e : 𝓞 E) : (A p).ιE (e : E) ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have h : IsIntegral ℤ ((A p).ιE (e : E)) := e.2.map (A p).ιE.toIntAlgHom
  exact h.tower_top
end Formalism.L2.SG.Pf.PCountEx
