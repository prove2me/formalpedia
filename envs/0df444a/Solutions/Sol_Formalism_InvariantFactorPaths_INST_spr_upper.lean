-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.spr_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:28.190154+00:00
-- url     : https://prove2.me/submissions/a0a07888-202d-4c4a-ac3e-6b7b35a2058b

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_bidet_le
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_support_induction

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (ν : Fin n → ℕ) (l : ℕ) (hl : ∀ t, ν t ≤ l)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) (m : Fin r × Fin n →₀ ℕ)
    (hm : m ∈ f.support) (a : Fin r) : rowDeg m a ≤ l := by
  refine spr_support_induction R r n ν (fun m => rowDeg m a ≤ l) ?_ f hf m hm
  intro K sz hsz I hsh hmono m hm
  exact spr_bidet_le R sz hsz I (fun k => (hmono k).injective) l (by rw [hsh]; exact hl) m hm a
end Formalism.InvariantFactorPaths.INST
