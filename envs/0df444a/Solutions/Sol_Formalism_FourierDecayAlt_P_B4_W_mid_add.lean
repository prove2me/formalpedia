-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.W_mid_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:21:47.978012+00:00
-- url     : https://prove2.me/submissions/83426e12-821b-4372-8e92-fef1055ade3d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_letter_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {F : Mat k r → E} (p q : List (Bool × Mat k r)) (b : Bool) {X Y : Mat k r}
    (hp : AllLie p) (hq : AllLie q) (hX : inLie k r X) (hY : inLie k r Y)
    (hF : CkOn ((p.length + 1 + q.length : ℕ) : ℕ∞) (GV k r) F) :
    ∀ g ∈ GV k r, W (p ++ (b, X + Y) :: q) F g = W (p ++ (b, X) :: q) F g + W (p ++ (b, Y) :: q) F g := by
  intro g hg
  simp only [W_append, W_cons]
  have hWq : CkOn ((p.length + 1 : ℕ) : ℕ∞) (GV k r) (W q F) := smooth_on_of_word_derivatives q hq (p.length + 1) hF
  have hWq1 : CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W q F) := ckOn_mono (by omega) hWq
  have hinner : ∀ h ∈ GV k r, op b (X + Y) (W q F) h = (op b X (W q F) + op b Y (W q F)) h :=
    fun h hh => op_letter_add b hX hY hWq1 hh
  rw [W_congr p hp hinner g hg]
  exact W_add p hp (ckOn_op p.length b hWq hX) (ckOn_op p.length b hWq hY) g hg
end Formalism.FourierDecayAlt.P.B4
