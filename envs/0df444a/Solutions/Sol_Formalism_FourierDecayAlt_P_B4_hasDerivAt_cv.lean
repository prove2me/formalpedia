-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.hasDerivAt_cv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:22:53.258797+00:00
-- url     : https://prove2.me/submissions/3348ced2-f759-4b37-9577-01e1d4b2796d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_diff

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
theorem _root_.solution {H : Mat k r → E} (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) {Z g : Mat k r}
    (hZ : inLie k r Z) (hg : g ∈ GV k r) (b : Bool) (σ : ℝ) :
    HasDerivAt (fun x : ℝ => H (cv b Z x g)) (op b Z H (cv b Z σ g)) σ := by
  have hg' : cv b Z σ g ∈ GV k r := cv_mem hZ hg σ
  have hd := ckOn_diff 0 b hH hZ hg'
  have h1 : HasDerivAt (fun s => H (cv b Z s (cv b Z σ g))) (op b Z H (cv b Z σ g)) 0 :=
    hd.hasDerivAt
  have h2 := HasDerivAt.comp_sub_const σ σ (by rw [sub_self]; exact h1)
  convert h2 using 1
  funext x
  rw [← cv_add]
  congr 2
  ring
end Formalism.FourierDecayAlt.P.B4
