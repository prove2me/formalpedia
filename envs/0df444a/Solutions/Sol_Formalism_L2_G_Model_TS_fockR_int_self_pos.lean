-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.fockR_int_self_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:00:51.680542+00:00
-- url     : https://prove2.me/submissions/7c836339-78dc-4764-8fc2-4badd0801a06

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial

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
theorem _root_.solution {σ : Type*} (f : MvPolynomial σ ℤ) (hf : f ≠ 0) : 0 < fockR f f := by
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; exact hf (MvPolynomial.support_eq_empty.mp h)
  unfold fockR
  refine Finset.sum_pos (fun m hm => ?_) hne
  have h1 : 0 < f.coeff m * f.coeff m := mul_self_pos.mpr (MvPolynomial.mem_support_iff.mp hm)
  have h2 : (0 : ℤ) < ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℤ) := by
    exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
  exact mul_pos h1 h2
end Formalism.L2.G.Model.TS
