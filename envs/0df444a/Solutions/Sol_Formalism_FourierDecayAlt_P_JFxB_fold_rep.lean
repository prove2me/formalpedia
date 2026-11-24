-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.fold_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:29.799257+00:00
-- url     : https://prove2.me/submissions/3532fa57-efb6-4491-a192-d01403595350

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_top_rep
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_foldL_ok

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution {O : Set (Mat k r)} (hO : IsOpen O) (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ {N : ℕ}, ts.length ≤ N → ∀ f : Mat k r → E, CkOn (N : ℕ∞) (O ∩ GV k r) f → ∀ g ∈ O, g ∈ GV k r →
      (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f g = wsum (foldL k r ts) f g := by
  induction ts with
  | nil =>
    intro N _ f _ g _ _
    simp [foldL, wsum, Rw]
  | cons t ts ih =>
    intro N hN f hf g hgO hgG
    have hN' : ts.length ≤ N := le_trans (Nat.le_succ _) hN
    have key := top_rep hO (foldL_ok (k := k) (r := r) ts) (by simpa using hN)
      (fun f => (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f)
      (fun f hf g hgO hgG => ih hN' f hf g hgO hgG) t.1 t.2.1 t.2.2 f hf g hgO hgG
    exact key
end Formalism.FourierDecayAlt.P.JFxB
