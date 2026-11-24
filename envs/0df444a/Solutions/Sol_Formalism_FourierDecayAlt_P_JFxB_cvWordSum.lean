-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.cvWordSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:26:11.196127+00:00
-- url     : https://prove2.me/submissions/52006ca0-e1fb-4038-b56e-b8d69e4cc563

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_qmL_ok
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_qminor_rep
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_unitL
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_unitL_ok
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_mdim0

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution : JF.CVWordSum := by
  intro k r Y
  refine ⟨unitL (qmL k r (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y)), ?_, ?_⟩
  · intro cw hcw
    have := unitL_ok (qmL_ok (k := k) (r := r) (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y)) cw hcw
    exact ⟨this.1, this.2.trans (le_of_eq mdim0)⟩
  · intro E _ _ UU f hf g hgU hgG
    obtain ⟨U, f', hU, hgU', hc, hff⟩ := hf g hgU
    have hf2 : CkOn ((Q.mdim k r 0 : ℕ) : ℕ∞) (U ∩ GV k r) f := by
      intro g₁ hg₁
      exact ⟨U, f', hU, hg₁.1, by rw [mdim0]; exact hc, hff⟩
    have := qminor_rep hU (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f hf2 g hgU' hgG
    show qminorOp (Q.EH k r) (Q.posL k r 0) (Q.posL k r 0) (Q.uC k r 0 Y) f g = _
    rw [this, ← wsum_unitL]
    rfl
end Formalism.FourierDecayAlt.P.JFxB
