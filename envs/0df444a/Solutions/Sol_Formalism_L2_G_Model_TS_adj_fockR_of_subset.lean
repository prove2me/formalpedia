-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.adj_fockR_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:15.811858+00:00
-- url     : https://prove2.me/submissions/ef91a3a2-afbd-48cd-b9bc-85fab2a1b9a9

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint

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
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model.TS
theorem _root_.solution {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ))
    (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) := by
  unfold fockR
  apply Finset.sum_subset h
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm]
  ring
end Formalism.L2.G.Model.TS
