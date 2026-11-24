-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.EH_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:35.933839+00:00
-- url     : https://prove2.me/submissions/b6d6bb30-a788-4a4b-bf25-04b92306bbf0

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xa_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xb_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dx
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_smul


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
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (c d : Fin (2 * r + k + 1)) (m : ℕ) (f : Mat k r → E)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (Q.EH k r c d f) := by
  rw [EH_eq]
  have hf' : CkOn ((m : ℕ∞) + 1) (GV k r) f := by exact_mod_cast hf
  exact CkOn_add (CkOn_Dx (x := (false, Xa k r c d)) (Xa_lie c d) hf')
    (CkOn_smul _ (CkOn_Dx (x := (false, Xb k r c d)) (Xb_lie c d) hf'))
end Formalism.FourierDecayAlt.P.JFxB
