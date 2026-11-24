-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.Dx_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:15:27.281026+00:00
-- url     : https://prove2.me/submissions/6c4340f1-5e42-4a26-9072-3dcbac4682c1

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_diff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution {x : Bool × B.Mat k r} (hx : inLie k r x.2) {F : B.Mat k r → ι → E} (hF : B.CkOn 1 (B.GV k r) F)
    (g : B.Mat k r) (hg : g ∈ B.GV k r) (i : ι) : Dx x F g i = Dx x (fun g => F g i) g := by
  have h := CkOn_diff hx hF hg hg
  have h2 := (hasDerivAt_pi.mp h) i
  rw [Dx_eq x (fun g => F g i) g]
  exact h2.deriv.symm
end Formalism.FourierDecayAlt.P.Ux8
