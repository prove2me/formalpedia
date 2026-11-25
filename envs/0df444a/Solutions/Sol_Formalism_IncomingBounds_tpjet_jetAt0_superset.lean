-- Prove2me | solution 1 for Formalism.IncomingBounds.tpjet_jetAt0_superset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:17.481952+00:00
-- url     : https://prove2.me/submissions/cc944e53-cf5e-4124-8951-730f84f593ff

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
variable {C : Type} [Field C]
namespace Formalism.IncomingBounds
theorem _root_.solution {σ : Type} (P : MvPolynomial σ C) (G : MvPowerSeries σ C)
    (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jetAt0 P G = ∑ m ∈ S, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]
end Formalism.IncomingBounds
