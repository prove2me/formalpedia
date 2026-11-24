-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.EHc_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:35.648361+00:00
-- url     : https://prove2.me/submissions/bdd4a770-2a2b-4720-8676-b3e725bd125f

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xa_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xb_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EHc_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dx
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_conj


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
theorem _root_.solution {y : Mat k r} (hy : y ∈ GV k r) (c d : Fin (2 * r + k + 1)) (m : ℕ) (f : Mat k r → E)
    (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (EHc k r y c d f) := by
  rw [EHc_eq]
  have hf' : CkOn ((m : ℕ∞) + 1) (GV k r) f := by exact_mod_cast hf
  exact CkOn_add (CkOn_Dx (x := (false, _)) (lie_conj (Xa_lie c d) hy) hf')
    (CkOn_smul _ (CkOn_Dx (x := (false, _)) (lie_conj (Xb_lie c d) hy) hf'))
end Formalism.FourierDecayAlt.P.JFxB
