-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.ins_sc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:22.855562+00:00
-- url     : https://prove2.me/submissions/1f4f1726-00ca-4a67-bfa5-f609f5207910

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_ins_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution (a : S) (φ : ℂ) :
    (ins a !![φ • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] : SlopeTestRemainingChoices S A) =
      Matrix.diagonal (fun e => if e a = 0 then algebraMap ℂ A φ else 1) := by
  have h1 : (φ • (1 : SlopeTestRemainingChoices S A)) = Matrix.diagonal (fun _ => algebraMap ℂ A φ) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]; congr 1; funext _
    simp [Algebra.algebraMap_eq_smul_one]
  have h2 : (1 : SlopeTestRemainingChoices S A) = Matrix.diagonal (fun _ => (1 : A)) := Matrix.diagonal_one.symm
  rw [h1]; conv_lhs => rw [h2]
  exact ins_diag a _ _
end Formalism.FourierDecayAlt.P.Fr2
