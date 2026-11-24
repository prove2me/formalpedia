-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.qminor_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:06:07.238958+00:00
-- url     : https://prove2.me/submissions/2c6436d0-9b76-48a1-a6e7-4f5d4718b7b2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_flatMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_fold_rep

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
theorem _root_.solution {O : Set (Mat k r)} (hO : IsOpen O) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (f : Mat k r → E) (hf : CkOn (t : ℕ∞) (O ∩ GV k r) f) (g : Mat k r) (hgO : g ∈ O) (hgG : g ∈ GV k r) :
    qminorOp (Q.EH k r) p q u f g = wsum (qmL k r p q u) f g := by
  have hfold : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun j : Fin t => Top (Q.EH k r) (u - ((j : ℕ) : ℂ)) (p (σ j)) (q j)).foldr (fun T h => T h) f g =
        wsum (foldL k r (tsOf p q u σ)) f g := by
    intro σ
    have := fold_rep hO (tsOf p q u σ) (N := t) (by simp [tsOf]) f hf g hgO hgG
    simpa [tsOf, List.map_ofFn, Function.comp_def] using this
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, hfold, qmL, wsum_flatMap, wsum_scale, Finset.sum_toList]
  first
  | exact (Finset.sum_toList _ _).symm
  | exact (Finset.sum_map_toList _ _).symm
  | simp [Finset.sum_toList]
end Formalism.FourierDecayAlt.P.JFxB
