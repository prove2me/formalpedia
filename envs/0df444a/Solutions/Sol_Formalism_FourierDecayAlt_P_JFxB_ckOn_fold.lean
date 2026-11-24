-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.ckOn_fold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:56:10.613187+00:00
-- url     : https://prove2.me/submissions/7ea6bbc1-3018-4f6d-b87a-790a0c1eff44

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_ckOn_top

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
theorem _root_.solution (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hS : ∀ c d (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Eop c d f))
    (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (m : ℕ) (f : Mat k r → E), CkOn ((m + ts.length : ℕ) : ℕ∞) (GV k r) f →
      CkOn (m : ℕ∞) (GV k r) ((ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) f) := by
  induction ts with
  | nil =>
    intro m f hf
    simpa using hf
  | cons t ts ih =>
    intro m f hf
    show CkOn (m : ℕ∞) (GV k r)
      (Top Eop t.1 t.2.1 t.2.2 ((ts.map fun t => Top Eop t.1 t.2.1 t.2.2).foldr (fun T h => T h) f))
    apply ckOn_top Eop hS
    apply ih (m + 1) f
    have e : m + 1 + ts.length = m + (t :: ts).length := by
      simp only [List.length_cons]
      omega
    rw [e]
    exact hf
end Formalism.FourierDecayAlt.P.JFxB
