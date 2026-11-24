-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.incl_z_iff_incl_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:55.208711+00:00
-- url     : https://prove2.me/submissions/5777035a-257a-428b-82cb-c05a2f5fab55

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_incl_R_of_Z
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_map_smul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_clear
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_incl_of_gens
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution : InclZIffR := by
  intro R _ _ _ l hl hu hd r n hn ν e
  constructor
  · intro hZ x hx
    exact la_incl_R_of_Z R r n hn ν l e hu hZ x hx
  · intro hR
    apply la_incl_of_gens r n hn ν l e hl
    intro g hg
    have h1 := hR _ (dualWeylMap ℤ R (Int.castRingHom R) r n ν g hg)
    obtain ⟨m, hm, f0, hf0, h2⟩ := la_clear R l hl hd hn ν _ h1
    refine ⟨m, hm, ?_⟩
    have h3 : map (Int.castRingHom R) (((m * l ^ e : ℕ) : ℤ) • g) = map (Int.castRingHom R) f0 := by
      rw [la_map_smul, ← h2, smul_smul]
      push_cast
      rfl
    have hinj : Function.Injective (map (Int.castRingHom R) :
        MvPolynomial (Fin r × Fin n) ℤ → MvPolynomial (Fin r × Fin n) R) :=
      map_injective _ (RingHom.injective_int (Int.castRingHom R))
    rw [hinj h3]
    exact hf0
end Formalism.CohomologicalDescent.LA
