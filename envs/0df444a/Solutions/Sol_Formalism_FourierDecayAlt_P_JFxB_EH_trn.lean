-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.EH_trn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:45.419704+00:00
-- url     : https://prove2.me/submissions/5a71d660-4b09-4903-96dd-232c00950b6e

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xa_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xb_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EHc_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_trn


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
theorem _root_.solution (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, Q.EH k r c d (trn L a b f) g = trn L a b (EHc k r b c d f) g := by
  intro g hg
  have hf1 : CkOn 1 (GV k r) f := by exact_mod_cast hf
  rw [EH_eq, EHc_eq]
  simp only
  rw [Dx_trn L ha hb (X := Xa k r c d) (Xa_lie c d) hf1 g hg, Dx_trn L ha hb (X := Xb k r c d) (Xb_lie c d) hf1 g hg]
  simp only [trn, map_add, map_smul]
end Formalism.FourierDecayAlt.P.JFxB
