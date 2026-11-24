-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x4.no_cut_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:34:59.297803+00:00
-- url     : https://prove2.me/submissions/9a93421c-c986-4ef1-a7d2-3881474e7368

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x4
theorem _root_.solution (w : Equiv.Perm (Fin m)) (a b j : Fin m) (hab : blk w a = blk w b)
    (hj1 : a ≤ j) (hj2 : j < b) : ¬ IsCut w j := by
  intro hcut
  classical
  have hss : Finset.univ.filter (fun c : Fin m => c < a ∧ IsCut w c) ⊂
      Finset.univ.filter (fun c : Fin m => c < b ∧ IsCut w c) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj2, hcut⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; exact absurd h (not_lt.mpr hj1)
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact ⟨lt_trans hc.1 (lt_of_le_of_lt hj1 hj2), hc.2⟩
  have := Finset.card_lt_card hss
  unfold blk at hab
  rw [hab] at this
  exact lt_irrefl _ this
end Formalism.FourierDecayAlt.P.C2x4
