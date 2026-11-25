-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.capelli_word_sum_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:15:37.268697+00:00
-- url     : https://prove2.me/submissions/202425f5-148f-495a-bcf8-5675970953c2

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_cvWordSumG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (k r : ℕ) (Y : ℂ) : ∃ L : List (ℂ × List (Formalism.FourierDecayAlt.B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, Formalism.FourierDecayAlt.B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (Formalism.FourierDecayAlt.B.Mat k r))
      (f : Formalism.FourierDecayAlt.B.Mat k r → E),
      Formalism.FourierDecayAlt.B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) UU f → ∀ g ∈ UU, g ∈ Formalism.FourierDecayAlt.B.GV k r →
        Formalism.FourierDecayAlt.Q.CV k r Y f g = (L.map fun cw => cw.1 • Formalism.FourierDecayAlt.B.Rw cw.2 f g).sum :=
  Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.cvWordSumG k r Y
end Formalism.FourierDecayAlt.P
