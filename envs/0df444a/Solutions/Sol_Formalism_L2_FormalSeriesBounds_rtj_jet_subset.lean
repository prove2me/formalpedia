-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_jet_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:33.131028+00:00
-- url     : https://prove2.me/submissions/f7689888-2327-46c2-b052-636e376745af

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (P : MvPolynomial σ K) (F : MvPowerSeries σ K) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    jetAt0 P F = ∑ m ∈ S, MvPolynomial.coeff m P * (mfact m : K) * MvPowerSeries.coeff m F := by
  unfold jetAt0
  exact Finset.sum_subset hS fun m _ hm => by
    rw [MvPolynomial.mem_support_iff, not_not] at hm
    rw [hm, zero_mul, zero_mul]
end Formalism.L2.FormalSeriesBounds
