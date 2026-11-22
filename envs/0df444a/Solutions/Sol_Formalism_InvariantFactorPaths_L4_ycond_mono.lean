-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.ycond_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:44.889802+00:00
-- url     : https://prove2.me/submissions/50d3c8fd-7e82-47a7-8686-b6d95f82a756

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycond


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] {N : ℕ} (LL : Letters N) (j : ℕ) (Mt Mt' : WithTop ℤ) (h : Mt ≤ Mt') :
    YCond p (r := r) LL j Mt ≤ YCond p LL j Mt' := by
  refine le_ycond LL j Mt' _ ?_ (fun c d x hx => ycond_glStable LL j Mt c d x hx)
  intro x hx
  have h1 := ycond_le_supp LL j Mt hx
  rw [mem_restrictSupport_iff] at h1 ⊢
  intro m hm
  exact le_trans (h1 hm) h
end Formalism.InvariantFactorPaths.L4
