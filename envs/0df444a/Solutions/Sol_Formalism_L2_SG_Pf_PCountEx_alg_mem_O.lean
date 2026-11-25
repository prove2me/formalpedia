-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.alg_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:16.756558+00:00
-- url     : https://prove2.me/submissions/748c6be6-04d7-4083-9628-c33c7ce72a30

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
theorem _root_.solution (p : HeightOneSpectrum (𝓞 F)) {t : (A p).Fp} (ht : t ∈ (haveI := (A p).lf; 𝒪[(A p).Fp])) :
    algebraMap (A p).Fp (A p).Ep t ∈ (A p).O := by
  haveI := (A p).lf
  rw [(A p).O_def]
  have h := isIntegral_algebraMap (R := 𝒪[(A p).Fp]) (A := (A p).Ep) (x := ⟨t, ht⟩)
  rw [IsScalarTower.algebraMap_apply 𝒪[(A p).Fp] (A p).Fp (A p).Ep] at h
  exact h
end Formalism.L2.SG.Pf.PCountEx
