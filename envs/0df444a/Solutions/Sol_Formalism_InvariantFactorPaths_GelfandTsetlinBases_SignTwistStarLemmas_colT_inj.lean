-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.colT_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:49.774262+00:00
-- url     : https://prove2.me/submissions/67b59183-5fd1-4c39-99a2-2a17b7230cfc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_idx_out

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open SignTwistStarLemmas
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution {μ : Fin n → ℤ} {lo hi : ℤ} (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hb : ∀ m, lo ≤ μ m ∧ μ m ≤ hi)
    {I I' : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (hI' : IsIndex μ I')
    (h : colT lo (hi - lo).toNat I = colT lo (hi - lo).toNat I') : I = I' := by
  funext c
  by_cases hc : c ∈ Finset.Ioc lo hi
  · rw [Finset.mem_Ioc] at hc
    have h1 := congrFun h ⟨(c - lo - 1).toNat, by omega⟩
    have e : lo + 1 + (((c - lo - 1).toNat : ℕ) : ℤ) = c := by omega
    simp only [colT, e, hatIdx] at h1
    split_ifs at h1
    · exact h1
    · exact compl_injective h1
  · rw [idx_out hlo hhi hb hI hc, idx_out hlo hhi hb hI' hc]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
