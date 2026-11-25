-- Prove2me | solution 1 for Formalism.L2.SG.Pf.PCountEx.approxF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:17:34.144308+00:00
-- url     : https://prove2.me/submissions/44dfefb0-34c7-49bb-8e30-b19b169b1f1a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SimpLemmas
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Theorems.Thm_UpperTheory_Reformulated_B_ApproximationIntegralOutsideFinset_approxF


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
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0) (b : ∀ p, (A p).Fp) :
    ∃ f : F, (∀ p ∈ S, haveI := (A p).lf
        valuation (A p).Fp ((A p).ιF f - b p) ≤ valuation (A p).Fp ((A p).ιF (algebraMap (𝓞 F) F c))) ∧
      ∀ p ∉ S, (A p).ιF f ∈ (haveI := (A p).lf; 𝒪[(A p).Fp]) :=
  by apply _root_.UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approxF <;> assumption
end Formalism.L2.SG.Pf.PCountEx
