-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_twist_monomial_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:50.782103+00:00
-- url     : https://prove2.me/submissions/9b5fc182-9654-4be9-9525-9fe9a3f65ecf

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_twistX_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_hom_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (al : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al (1 : R)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F (-flt_cost LL S bm al) :=
  flt_hom_monomial (laurentCoeffFiltration R n (ι × Fin n) e) (twistSub LL S j) (-flt_cost LL S bm)
    (fun w => flt_twistX_mem LL S j h w) al
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
