-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.spr_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:48:31.944437+00:00
-- url     : https://prove2.me/submissions/a1d5a462-b10f-4487-ac76-918b06310389

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_le_bidet
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
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (ν : Fin n → ℕ) (lo : ℕ) (hlo : ∀ t, lo ≤ ν t)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ dualWeyl R n n ν) (m : Fin n × Fin n →₀ ℕ)
    (hm : m ∈ f.support) (a : Fin n) : lo ≤ rowDeg m a := by
  refine spr_support_induction R n n ν (fun m => lo ≤ rowDeg m a) ?_ f hf m hm
  intro K sz hsz I hsh hmono m hm
  exact spr_le_bidet R sz hsz I (fun k => (hmono k).injective) lo (by rw [hsh]; exact hlo) m hm a
end Formalism.InvariantFactorPaths.INST
